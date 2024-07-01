#include "all.h"

#define NOBID (-1u)

static int
isconbits(Fn *fn, Ref r)
{
	return rtype(r) == RCon && fn->con[r.val].type == CBits;
}

/* special case of trivial load/store offset address calculation */
/* %t =l add %t1, n - where %t is used only as a load/store addr in the same blk*/
static int
isldstaddr(Fn *fn, Blk *b, Ins *i)
{
	Tmp *t;
	Use *u;

	if (i->op == Oadd)
	if (i->cls == Kl)
	if (isconbits(fn, i->arg[0]) || isconbits(fn, i->arg[1])) {
		assert(rtype(i->to) == RTmp);
		t = &fn->tmp[i->to.val];
		if (!t->nuse)
			return 0;
		for (u = t->use; u < &t->use[t->nuse]; u++) {
			if (u->type != UIns || u->bid != b->id)
				return 0;
			if (!isload(u->u.ins->op) && !isstore(u->u.ins->op))
				return 0;
		}
		return 1;
	}
	return 0;
}

/* special case of cmp instruction used only as jnz param */
static int
iscmp4jnz(Fn *fn, Ins *i)
{
	Tmp *t;
	int x;

	if (iscmp(i->op, &x, &x)) {
		assert(rtype(i->to) == RTmp);
		t = &fn->tmp[i->to.val];
		if (t->nuse == 1) {
			if (t->use[0].type == UJmp)
				return 1;
			if (t->use[0].type == UIns)
			if (iscmp(t->use[0].u.ins->op, &x, &x))
				return 1;
		}
	}
	return 0;
}

/* instructions that do not benefit from GVN/GCM */
int
isbad4gcm(Fn *fn, Blk *b, Ins *i)
{
	return isldstaddr(fn, b, i) || iscmp4jnz(fn, i);
}

/* ins can trap at runtime */
static int
istrapping(Ins *i)
{
	if (i->cls == Ks || i->cls == Kd)
		return 0;
	return INRANGE(i->op, Odiv, Ourem);
}

/* fixed ins that can be eliminated if unused */
static int
canelim(Ins *i)
{
	int x;
	return isload(i->op) || isalloc(i->op) || istrapping(i)
		|| i->op == Oadd || iscmp(i->op, &x, &x);
}

/* ins must stay in def blk */
static int
isfixed(Fn *fn, Blk *b, Ins *i)
{
	return optab[i->op].ispinned || istrapping(i) || isbad4gcm(fn, b, i);
}

static uint earlyins(Fn *, Blk *, Ins *);

/* return earlybid of ref def ins */
static uint
schedearly(Fn *fn, Ref r)
{
	Tmp *t;
	Blk *b;

	if (rtype(r) != RTmp)
		return 0 /* root/start */;

	t = &fn->tmp[r.val];
	if (t->gcmbid != NOBID)
		return t->gcmbid; /* already visited/visiting */

	b = fn->rpo[t->bid];
	if (t->def) {
		/* def is an ins */
		assert(b->ins <= t->def && t->def < &b->ins[b->nins]);
		t->gcmbid = 0; /* mark visiting root/start blk */
		t->gcmbid = earlyins(fn, b, t->def); /* schedule ins input defs */
	} else {
		/* def is a phi - it stays in its def blk */
		t->gcmbid = t->bid;
	}

	return t->gcmbid;
}

/* return deepest domdpth bid of arg defs */
static uint
earlyins(Fn *fn, Blk *b, Ins* i)
{
	uint earlybid, arg1earlybid;

	earlybid = schedearly(fn, i->arg[0]);
	assert(earlybid != NOBID);
	arg1earlybid = schedearly(fn, i->arg[1]);
	assert(arg1earlybid != NOBID);
	if (fn->rpo[earlybid]->domdpth < fn->rpo[arg1earlybid]->domdpth) {
		assert(dom(fn->rpo[earlybid], fn->rpo[arg1earlybid]));
		earlybid = arg1earlybid;
	}

	/* fixed ins remain in their defining blk */
	return isfixed(fn, b, i) ? b->id : earlybid;
}

static void
earlyblk(Fn *fn, uint bid)
{
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;

	b = fn->rpo[bid];
	for (p = b->phi; p; p = p->link)
		for (n = 0; n < p->narg; n++)
			schedearly(fn, p->arg[n]);
	for (i = b->ins; i < &b->ins[b->nins]; i++)
		if (isfixed(fn, b, i))
			earlyins(fn, b, i);
	schedearly(fn, b->jmp.arg);
}

/* least common ancestor in dom tree */
static uint
lcabid(Fn *fn, uint bid1, uint bid2)
{
	Blk *b;

	if (bid1 == NOBID)
		return bid2;
	if (bid2 == NOBID)
		return bid1;

	b = lca(fn->rpo[bid1], fn->rpo[bid2]);
	assert(b);
	return b->id;
}

static uint
bestbid(Fn *fn, uint earlybid, uint latebid)
{
	Blk *curb, *earlyb, *bestb;

	if (latebid == NOBID)
		return NOBID; /* unused */

	assert(earlybid != NOBID);

	earlyb = fn->rpo[earlybid];
	bestb = curb = fn->rpo[latebid];
	assert(dom(earlyb, curb));

	while (curb != earlyb) {
		curb = curb->idom;
		if (curb->loop < bestb->loop)
			bestb = curb;
	}
	return bestb->id;
}

static uint lateins(Fn *, Blk *, Ins *, Ref r);
static uint latephi(Fn *, Phi *, Ref r);
static uint latejmp(Blk *, Ref r);

/* return lca bid of ref uses */
static uint
schedlate(Fn *fn, Ref r)
{
	Tmp *t;
	Blk *b;
	Use *u;
	uint earlybid;
	uint latebid;
	uint uselatebid;

	if (rtype(r) != RTmp)
		return NOBID;

	t = &fn->tmp[r.val];
	if (t->visit)
		return t->gcmbid; /* already visited/visiting */

	t->visit = 1; /* mark visiting/visited */
	earlybid = t->gcmbid;
	if (earlybid == NOBID)
		return NOBID; /* not used */
	t->gcmbid = t->bid; /* t->gcmbid is now latebid */

	latebid = NOBID;
	for (u = t->use; u < &t->use[t->nuse]; u++) {
		assert(u->bid < fn->nblk);
		b = fn->rpo[u->bid];
		switch (u->type) {
		case UXXX:
			die("unreachable");
			break;
		case UPhi:
			uselatebid = latephi(fn, u->u.phi, r);
			break;
		case UIns:
			uselatebid = lateins(fn, b, u->u.ins, r);
			break;
		case UJmp:
			uselatebid = latejmp(b, r);
			break;
		}
		latebid = lcabid(fn, latebid, uselatebid);
	}

	/* phis stay in their def blk */
	if (t->def) {
		/* allow elimination of unused load/alloc/trapping ins */
		if (latebid == NOBID && canelim(t->def))
			t->gcmbid = NOBID;
		/* ... otherwise fixed ins stay in defining blk */
		else if(!isfixed(fn, fn->rpo[t->bid], t->def))
			t->gcmbid = bestbid(fn, earlybid, latebid);
	}

	return t->gcmbid;
}

/* return lca bid of uses, or NOBID if no active uses */
static uint
lateins(Fn *fn, Blk *b, Ins *i, Ref r)
{
	uint latebid;

	assert(i->op == Onop || req(i->arg[0], r) || req(i->arg[1], r));
	if (i->op == Onop)
		return NOBID; /* already eliminated */

	assert(b->ins <= i && i < &b->ins[b->nins]);

	latebid = schedlate(fn, i->to);
	/* allow elimination of unused load/alloc/trapping ins */
	if (latebid == NOBID)
	if (canelim(i))
		return NOBID;
	/* ... otherwise fixed ins stay in defining blk */
	return isfixed(fn, b, i) ? b->id : latebid;
}

static uint
latephi(Fn *fn, Phi *p, Ref r)
{
	uint n;
	uint latebid;

	if (!p->narg)
		return NOBID; /* marked as unused */

	latebid = NOBID;
	for (n = 0; n < p->narg; n++)
		if (req(p->arg[n], r))
			latebid = lcabid(fn, latebid, p->blk[n]->id);

	assert(latebid != NOBID);
	return latebid;
}

static uint
latejmp(Blk *b, Ref r)
{
	if (req(b->jmp.arg, R))
		return NOBID;
	else {
		assert(req(b->jmp.arg, r));
		return b->id;
	}
}

static void
lateblk(Fn *fn, uint bid)
{
	Blk *b;
	Phi **pp;
	Ins *i;

	b = fn->rpo[bid];
	for (pp = &b->phi; *(pp);)
		if (schedlate(fn, (*pp)->to) == NOBID) {
			/* unused */
			(*pp)->narg = 0; /* mark unused */
			*pp = (*pp)->link; /* remove phi */
		} else
			pp = &(*pp)->link;

	for (i = b->ins; i < &b->ins[b->nins]; i++)
		if (isfixed(fn, b, i))
		    lateins(fn, b, i, i->arg[0]);
}

/* recreate b->ins for blks with new ins */
static void
sched(Fn *fn)
{
	Blk *b;
	Ins *i;
	Tmp *t;
	uint bid, nins;
	BSet to[1];
	uint *bnins, *newbnins;
	Ins **newbins;

	/* find blks with new ins; count ins in each blk after gcm */
	bsinit(to, fn->nblk); /* no free for BSet? */
	bnins = emalloc(fn->nblk * sizeof bnins[0]);
	for (bid = 0; bid < fn->nblk; bid++) {
		b = fn->rpo[bid];
		for (i = b->ins; i < &b->ins[b->nins]; i++) {
			if (i->op == Onop)
				continue; /* already eliminated */
			if (isfixed(fn, b, i) && !canelim(i)) {
				bnins[bid]++;
				continue;
			}
			assert(rtype(i->to) == RTmp);
			t = &fn->tmp[i->to.val];
			if (t->gcmbid != NOBID) {
				bnins[t->gcmbid]++;
				if (t->gcmbid != bid)
					bsset(to, t->gcmbid);
			}
		}
	}

	/* allocate new b->ins for blks with new ins */
	newbins = emalloc(fn->nblk * sizeof newbins[0]);
	for (bid = 0; bid < fn->nblk; bid++) {
		if (!bshas(to, bid))
			continue;
		nins = bnins[bid];
		newbins[bid] = alloc(nins * sizeof(Ins));
	}

	/* populate new b->ins */
	newbnins = emalloc(fn->nblk * sizeof newbins[0]);
	for (bid = 0; bid < fn->nblk; bid++) {
		b = fn->rpo[bid];
		for (i = b->ins; i < &b->ins[b->nins]; i++) {
			if (i->op == Onop)
				continue; /* already eliminated */
			if(isfixed(fn, b, i) && !canelim(i)) {
				if (bshas(to, bid))
					newbins[bid][newbnins[bid]++] = *i;
				continue;
			}
			assert(rtype(i->to) == RTmp);
			t = &fn->tmp[i->to.val];
			if (t->gcmbid == NOBID)
				*i = (Ins){.op = Onop};
			else {
				if (bshas(to, t->gcmbid)) {
					newbins[t->gcmbid][newbnins[t->gcmbid]++] = *i;
				}
				if (t->gcmbid != bid)
					*i = (Ins){.op = Onop};
			}
		}
	}

	/* install new b->ins */
	for (bid = 0; bid < fn->nblk; bid++) {
		if (!bshas(to, bid))
			continue;
		b = fn->rpo[bid];
		b->ins = newbins[bid];
		b->nins = newbnins[bid];
	}

	free(bnins);
	free(newbins);
	free(newbnins);
}

static void
cleartmps(Fn *fn)
{
	Tmp *t;

	for (t=&fn->tmp[Tmp0]; t < &fn->tmp[fn->ntmp]; t++) {
		t->visit = 0;
		t->gcmbid = NOBID;
	}
}

/* https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf */
/* require use dom */
/* maintains rpo pred dom */
/* breaks use */
void
gcm(Fn *fn)
{
	uint bid;

	filldomdpth(fn);
	fillloop(fn);

	cleartmps(fn);
	for (bid=0; bid<fn->nblk; bid++)
		earlyblk(fn, bid);

	for (bid=0; bid<fn->nblk; bid++)
		lateblk(fn, bid);

	sched(fn);

	cleartmps(fn);

	if (debug['G']) {
		fprintf(stderr, "\n> After GCM:\n");
		printfn(fn, stderr);
	}
}
