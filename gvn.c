#include "all.h"

/* blk unreachable? */
static int
isdead(Fn *fn, Blk *b) {
	if (b == fn->start)
		return 0;
	if (b->npred == 0)
		return 1;
	if (b->npred == 1 && b->pred[0] == b)
		return 1;
	return 0;
}

/* literal constants 0, 1 */
static Ref con01[2];

/* is the ref a boolean - 0, 1 - value? */
static int
iswu1(Fn *fn, Ref r)
{
	Tmp *t;
	int x;

	if (req(r, con01[0]) || req(r, con01[1]))
		return 1;
	if (rtype(r) != RTmp)
		return 0;
	t = &fn->tmp[r.val];
	if (t->cls != Kw || !t->def)
		return 0;
	if (iscmp(t->def->op, &x, &x))
		return 1;
	if (t->def->op == Oand)
	if (req(t->def->arg[0], con01[1]) || req(t->def->arg[1], con01[1]))
		return 1;
	if (t->def->op == Oand || t->def->op == Oor || t->def->op == Oxor)
		return iswu1(fn, t->def->arg[0]) && iswu1(fn, t->def->arg[1]);
	if (isext(t->def->op))
		return iswu1(fn, t->def->arg[0]);
	return 0;
}

static inline uint
mix(uint x0, uint x1)
{
	return x0 + 17*x1;
}

static inline uint
rhash(Ref r)
{
	return mix(r.type, r.val);
}

static uint
ihash(Ins *i)
{
	uint a0h, a1h, ah, h;

	a0h = rhash(i->arg[0]);
	a1h = rhash(i->arg[1]);
	if (optab[i->op].commutes)
		ah = mix(a0h, a0h) ^ mix(a1h, a1h);
	else
		ah = mix(a0h, a1h);

	h = mix(i->cls, i->op);
	h = mix(h, ah);

	return h;

}

static int
ieq(Ins *ia, Ins *ib)
{
	if (ia->cls == ib->cls)
	if (ia->op == ib->op) {
		if (req(ia->arg[0], ib->arg[0]))
		if (req(ia->arg[1], ib->arg[1]))
                       return 1;
		if (optab[ia->op].commutes)
		if (req(ia->arg[0], ib->arg[1]))
		if (req(ia->arg[1], ib->arg[0]))
                       return 1;
	}
	return 0;
}

static Ins** gvntbl;
static uint gvntbln;
static uint lookupn;
static uint proben;
static uint maxproben;

static Ins *
gvndup(Ins *i, int insert) {
	uint idx, n;
	Ins *i2;

	lookupn++;

	idx = ihash(i) % gvntbln;
	for (n = 1;; n++) {
		proben++;
		if (n > maxproben)
			maxproben = n;
		i2 = gvntbl[idx];
		if (!i2)
			break;
		if (ieq(i, i2))
			return i2;

		idx++;
		if (gvntbln <= idx)
			idx = 0;
	}
	/* not found */
	if (insert) {
		gvntbl[idx] = i;
	}
	return 0;
}

static void
replaceref(Ref *r, Ref r1, Ref r2)
{
	if (req(*r, r1))
		*r = r2;
}

static void
replacepuse(Phi *p, Ref r1, Ref r2)
{
	Ref *a;

	for (a = p->arg; a < &p->arg[p->narg]; a++)
		replaceref(a, r1, r2);
}

static void
replaceiuse(Ins *i, Ref r1, Ref r2)
{
	replaceref(&i->arg[0], r1, r2);
	replaceref(&i->arg[1], r1, r2);
}

static void
replacejuse(Blk* b, Ref r1, Ref r2)
{
	replaceref(&b->jmp.arg, r1, r2);
}

static void
replaceuse(Fn *fn, Use* u, Ref r1, Ref r2)
{
	Tmp *t2;
	Blk *b;

	t2 = rtype(r2) == RTmp ? &fn->tmp[r2.val] : 0;
	b = fn->rpo[u->bid];

	switch (u->type) {
	case UXXX:
		die("unreachable");
		break;
	case UPhi:
		replacepuse(u->u.phi, r1, r2);
		if (t2)
			adduse(t2, UPhi, b, u->u.phi);
		break;
	case UIns:
		replaceiuse(u->u.ins, r1, r2);
		if (t2)
			adduse(t2, UIns, b, u->u.ins);
		break;
	case UJmp:
		replacejuse(fn->rpo[u->bid], r1, r2);
		if (t2)
			adduse(t2, UJmp, b);
		break;
	}
}

static void
replaceuses(Fn *fn, Ref r1, Ref r2)
{
	Tmp *t1;
	Use *u;

	assert(rtype(r1) == RTmp);
	t1 = &fn->tmp[r1.val];

	for (u = t1->use; u < &t1->use[t1->nuse]; u++)
		replaceuse(fn, u, r1, r2);

	t1->nuse = 0;
}

/* sort phi args in blk pred order */
static void
phinorm(Blk *b, Phi *p)
{
	Blk *pred, *btmp;
	Ref atmp;
	uint n, n1;

	assert(b->npred == p->narg);
	/* bubble sort :) */
	for (n = 0; n < b->npred; n++) {
		pred = b->pred[n];
		if (p->blk[n] != pred) {
			for (n1 = n+1; n1 < b->npred; n1++)
				if (p->blk[n1] == pred)
					break;
			assert(n1 < b->npred);
			atmp = p->arg[n1];
			btmp = p->blk[n1];
			p->arg[n1] = p->arg[n];
			p->blk[n1] = p->blk[n];
			p->arg[n] = atmp;
			p->blk[n] = btmp;
		}
	}
}

static int
rcmp(Ref a, Ref b)
{
	if (rtype(a) != rtype(b))
		return rtype(a)-rtype(b);
	return a.val - b.val;
}

static int
phicmp(const void *a, const void *b)
{
	Phi *pa, *pb;
	uint n;
	int acmp;

	pa = *(Phi**)a;
	pb = *(Phi**)b;
	assert(pa->narg == pb->narg);
	for (n=0; n<pa->narg; n++) {
		assert(pa->blk[n] == pb->blk[n]);
		acmp = rcmp(pa->arg[n], pb->arg[n]);
		if (acmp != 0)
			return acmp;
	}
	return 0;
}

static int
phieq(Phi *pa, Phi *pb)
{
	uint n;

	assert(pa->narg == pb->narg);
	for (n=0; n<pa->narg; n++) {
		assert(pa->blk[n] == pb->blk[n]);
		if (!req(pa->arg[n], pb->arg[n]))
			return 0;
	}
	return 1;
}

static void
dedupphis(Fn *fn, Blk *b) {
	uint n, nphis;
	Blk *b2;
	Phi *p, **pp, **phis;
	int dups;

	/* phi "copy" - all args identical */
	for (pp = &b->phi; *pp;) {
		p = *pp;
		assert(p->narg == b->npred);
		for (n = 0; n < p->narg-1; n++) {
			if (!req(p->arg[n], p->arg[n+1]))
				goto Skip;
		}
		replaceuses(fn, p->to, p->arg[0]);
		p->narg = 0; /* mark as unused */
		*pp = (*pp)->link;
		continue;
	Skip:;
		pp = &(*pp)->link;
	}

	/* phi bool 1/0 "copy" */
	/* TODO - triangle case */
	if (b->npred == 2)
	if (b->pred[0]->npred == 1)
	if (b->pred[1]->npred == 1)
	if (b->pred[0]->pred[0] == b->pred[1]->pred[0]) {
		b2 = b->pred[0]->pred[0];
		assert(b2->jmp.type == Jjnz);
		if (iswu1(fn, b2->jmp.arg)) {
			// fprintf(stderr, "\n@%s candidate for phi bool copy elim\n", b->name);
			for (pp = &b->phi; *pp;) {
				p = *pp;
				assert(p->narg == 2);
				if (!req(p->arg[0], con01[p->blk[0] == b2->s1]))
					goto Skip2;
				if (!req(p->arg[1], con01[p->blk[0] == b2->s2]))
					goto Skip2;
				replaceuses(fn, p->to, b2->jmp.arg);
				p->narg = 0; /* mark as unused */
				*pp = (*pp)->link;
				continue;
			Skip2:;
				pp = &(*pp)->link;
			}
		}
	}

	/* redundant phis */
	if (!b->phi || !b->phi->link)
		return;
	nphis = 0;
	for (p = b->phi; p; p = p->link) {
		nphis++;
		phinorm(b, p);
	}
	phis = emalloc(nphis * sizeof phis[0]);
	n = 0;
	for (p = b->phi; p; p = p->link)
		phis[n++] = p;
	qsort(phis, nphis, sizeof phis[0], phicmp);
	dups = 0;
	p = phis[0];
	for (n = 1; n < nphis; n++)
		if (phieq(p, phis[n])) {
			dups = 1;
			replaceuses(fn, phis[n]->to, p->to);
			phis[n]->narg = 0; /* mark as unused */
			phis[n] = 0;
		} else
			p = phis[n];
	if (dups) {
		pp = &b->phi;
		for (n = 0; n < nphis; n++)
			if (phis[n]) {
				*pp = phis[n];
				pp = &phis[n]->link;
			}
		*pp = 0;
	}
	free(phis);
}

static int
iscon(Con *c, int cls, int64_t v)
{
	if (c->type != CBits)
		return 0;
	switch (cls) {
	case Kw: return (int32_t)c->bits.i == (int32_t)v;
	case Kl: return c->bits.i == v;
	case Ks: return c->bits.s == (float)v;
	case Kd: return c->bits.d == (double)v;
	}
	die("unreachable");
	return 0;
}

static int
isconref(Fn *fn, Ref r, int cls, int64_t v)
{
	if (rtype(r) != RCon)
		return 0;
	return iscon(&fn->con[r.val], cls, v);
}

static Ref
copyarg(Fn *fn, Ins *i)
{
	static bits extcpy[] = {
		[WFull] = 0,
		[Wsb] = BIT(Wsb) | BIT(Wsh) | BIT(Wsw),
		[Wub] = BIT(Wub) | BIT(Wuh) | BIT(Wuw),
		[Wsh] = BIT(Wsh) | BIT(Wsw),
		[Wuh] = BIT(Wuh) | BIT(Wuw),
		[Wsw] = BIT(Wsw),
		[Wuw] = BIT(Wuw),
	};
	bits b;
	Tmp *t;

	if (i->op == Ocopy)
		return i->arg[0];

	if (optab[i->op].hasid) {
		if (isconref(fn, i->arg[1], i->cls, optab[i->op].idval))
		if (!optab[i->op].iscmpeq || iswu1(fn, i->arg[0]))
			return i->arg[0];
		if (optab[i->op].commutes)
		if (isconref(fn, i->arg[0], i->cls, optab[i->op].idval))
		if (!optab[i->op].iscmpeq || iswu1(fn, i->arg[1]))
			return i->arg[1];
	}

	if (optab[i->op].idemp)
	if (req(i->arg[0], i->arg[1]))
		return i->arg[1];

	if (optab[i->op].iscmpeq) {
		if (req(i->arg[0], i->arg[1]))
			return con01[optab[i->op].eqval];
		// TODO - check - assumes Cons, Syms are deduped
		if (rtype(i->arg[0]) == RCon && rtype(i->arg[1]) == RCon)
			return con01[1-optab[i->op].eqval];
	}

	if (!isext(i->op) || rtype(i->arg[0]) != RTmp)
		return R;
	if (i->op == Oextsw || i->op == Oextuw)
	if (i->cls == Kw)
		return i->arg[0];
	if (iswu1(fn, i->arg[0]))
		return i->arg[0];

	t = &fn->tmp[i->arg[0].val];
	assert(KBASE(t->cls) == 0);
	if (i->cls == Kl && t->cls == Kw)
		return R;
	b = extcpy[t->width];
	return (BIT(Wsb + (i->op-Oextsb)) & b) != 0 ? i->arg[0] : R;
}

static Ref opfold(int, int, Con *, Con *, Fn *);

static Ref
foldval(Fn *fn, Ins *i)
{
	Ref rr;
	Con *cl, *cr;

	if (rtype(i->to) != RTmp)
		return R;
	if (optab[i->op].canfold) {
		if (rtype(i->arg[0]) != RCon)
			return R;
		cl = &fn->con[i->arg[0].val];
		rr = i->arg[1];
		if (req(rr, R))
		    rr = CON_Z;
		if (rtype(rr) != RCon)
			return R;
		cr = &fn->con[rr.val];

		return opfold(i->op, i->cls, cl, cr, fn);
	}
	return R;
}

/* truncate constant bits to 32 bits for "s"/w" uses */
static void
con32(Fn *fn, Ins *i)
{
	uint n;
	int argcls;
	Con *c;
	int64_t bits32;

	for (n = 0; n < 2; n++) {
		if (rtype(i->arg[n]) != RCon)
			continue;
		argcls = optab[i->op].argcls[n][i->cls];
		if (argcls == Kx || KWIDE(argcls))
			continue;
		c = &fn->con[i->arg[n].val];
		if (c->type != CBits)
			continue;
		bits32 = c->bits.i & 0xffffffff;
		if (bits32 == c->bits.i)
			continue;
		i->arg[n] = getcon(bits32, fn);
	}
}

static int
skipdedup(Fn *fn, Blk *b, Ins *i)
{
	return isbad4gcm(fn, b, i);
}

static void
dedupi(Fn *fn, Blk *b, Ins *i)
{
	Ref r2;
	Ins *i2;

	if (i->op == Onop)
		return;

	con32(fn, i);

	if (optab[i->op].ispinned)
		return;

	/* effective copy? */
	r2 = copyarg(fn, i);
	if (!req(r2, R)) {
		replaceuses(fn, i->to, r2);
		*i = (Ins){.op = Onop};
		return;
	}

	/* effective constant? */
	r2 = foldval(fn, i);
	if (!req(r2, R)) {
		replaceuses(fn, i->to, r2);
		*i = (Ins){.op = Onop};
		return;
	}

	if (skipdedup(fn, b, i))
		return;

	/* duplicate? */
	i2 = gvndup(i, 1);
	if (i2) {
		replaceuses(fn, i->to, i2->to);
		*i = (Ins){.op = Onop};
		return;
	}
}

static void
dedupins(Fn *fn, Blk *b)
{
	Ins *i;

	for (i = b->ins; i < &b->ins[b->nins]; i++)
		dedupi(fn, b, i);
}

static void
dedupjmp(Fn *fn, Blk *b) {
	Blk *tmp;
	Con *c;
	if (b->jmp.type != Jjnz)
		return;
	if (b->s1 != b->s2) {
		if (rtype(b->jmp.arg) != RCon)
			return;
		c = &fn->con[b->jmp.arg.val];
		if (c->type != CBits)
			return;
		if (isconref(fn, b->jmp.arg, Kw, 0)) {
			tmp = b->s1;
			b->s1 = b->s2;
			b->s2 = tmp;
		}
	}
	/* we later move active ins out of dead blks */
	edgedel(b, &b->s2);
	b->jmp.type = Jjmp;
	b->jmp.arg = R;
}

/* propagate dead blks */
static int
deadblk(Fn *fn, Blk *b) {
	if (!isdead(fn, b))
		return 0;
	if (b->s1)
		edgedel(b, &b->s1);
	if (b->s2)
		edgedel(b, &b->s2);
	b->jmp.type = Jhlt;
	b->jmp.arg = R;
	return 1;
}

/* rebuild rpo pred use */
/* careful not to lose active ins */
static void
rebuildcfg(Fn *fn) {
	uint n, prevnblk, nins;
	Blk **prevrpo;
	Blk *b;
	Ins *i, *iv;

	prevnblk = fn->nblk;
	prevrpo = emalloc(prevnblk * sizeof prevrpo[0]);
	memcpy(prevrpo, fn->rpo, prevnblk * sizeof prevrpo[0]);

	fillrpo(fn);

	iv = 0;
	for (n=0; n<prevnblk; n++) {
		b = prevrpo[n];
		if (b->id == -1u) {
			/* blk unreachable after GVN */
			for (i = b->ins; i < &b->ins[b->nins]; i++)
				if (i->op != Onop)
				if (!optab[i->op].ispinned)
				if (gvndup(i, 0) == i) {
					/* (possibly) active ins - add to start blk */
					if (!iv) {
						nins = fn->start->nins;
						iv = vnew(nins, sizeof iv[0], PHeap);
						memcpy(iv, fn->start->ins, nins * sizeof iv[0]);
					}
					vgrow(&iv, ++nins);
					iv[nins-1] = *i;
				}
		}
	}
	if (iv) {
		idup(&fn->start->ins, iv, nins);
		fn->start->nins = nins;
		vfree(iv);
	}
	free(prevrpo);
}

/* https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf */
/* require rpo pred ssa use */
/* recreates rpo */
/* breaks pred use dom ssa (GCM fixes ssa) */
void
gvn(Fn *fn)
{
	uint n, nins;
	Blk *b;

	con01[0] = getcon(0, fn);
	con01[1] = getcon(1, fn);

	nins = 0;
	for (b=fn->start; b; b=b->link)
		nins += b->nins;

	gvntbln = nins + nins/2;
	gvntbl = emalloc(gvntbln * sizeof gvntbl[0]);
	lookupn = 0;
	proben = 0;
	maxproben = 0;

	/* GVN */
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		if (deadblk(fn, b))
			continue;
		dedupphis(fn, b);
		dedupins(fn, b);
		dedupjmp(fn, b);
	}

	rebuildcfg(fn);

	free(gvntbl);
	gvntbl = 0;
	gvntbln = 0;
	lookupn = 0;
	proben = 0;
	maxproben = 0;

	if (debug['G']) {
		fprintf(stderr, "\n> After GVN:\n");
		printfn(fn, stderr);
	}
}

/* boring folding code */

static int
foldint(Con *res, int op, int cls, Con *cl, Con *cr)
{
	union {
		int64_t s;
		uint64_t u;
		float fs;
		double fd;
	} l, r;
	uint64_t x;
	Sym sym;
	int typ;
	int w;

	w = cls == Kl;
	memset(&sym, 0, sizeof sym);
	typ = CBits;
	l.s = cl->bits.i;
	r.s = cr->bits.i;
	if (op == Oadd) {
		if (cl->type == CAddr) {
			if (cr->type == CAddr)
				return 1;
			typ = CAddr;
			sym = cl->sym;
		}
		else if (cr->type == CAddr) {
			typ = CAddr;
			sym = cr->sym;
		}
	}
	else if (op == Osub) {
		if (cl->type == CAddr) {
			if (cr->type != CAddr) {
				typ = CAddr;
				sym = cl->sym;
			} else if (!symeq(cl->sym, cr->sym))
				return 1;
		}
		else if (cr->type == CAddr)
			return 1;
	}
	else if (cl->type == CAddr || cr->type == CAddr)
		return 1;
	if (op == Odiv || op == Orem || op == Oudiv || op == Ourem) {
		if (iscon(cr, cls, 0))
			return 1;
		if (op == Odiv || op == Orem) {
			x = w ? INT64_MIN : INT32_MIN;
			if (iscon(cr, cls, -1))
			if (iscon(cl, cls, x))
				return 1;
		}
	}
	switch (op) {
	case Oadd:  x = l.u + r.u; break;
	case Osub:  x = l.u - r.u; break;
	case Oneg:  x = -l.u; break;
	case Odiv:  x = w ? l.s / r.s : (int32_t)l.s / (int32_t)r.s; break;
	case Orem:  x = w ? l.s % r.s : (int32_t)l.s % (int32_t)r.s; break;
	case Oudiv: x = w ? l.u / r.u : (uint32_t)l.u / (uint32_t)r.u; break;
	case Ourem: x = w ? l.u % r.u : (uint32_t)l.u % (uint32_t)r.u; break;
	case Omul:  x = l.u * r.u; break;
	case Oand:  x = l.u & r.u; break;
	case Oor:   x = l.u | r.u; break;
	case Oxor:  x = l.u ^ r.u; break;
	case Osar:  x = (w ? l.s : (int32_t)l.s) >> (r.u & (31|w<<5)); break;
	case Oshr:  x = (w ? l.u : (uint32_t)l.u) >> (r.u & (31|w<<5)); break;
	case Oshl:  x = l.u << (r.u & (31|w<<5)); break;
	case Oextsb: x = (int8_t)l.u;   break;
	case Oextub: x = (uint8_t)l.u;  break;
	case Oextsh: x = (int16_t)l.u;  break;
	case Oextuh: x = (uint16_t)l.u; break;
	case Oextsw: x = (int32_t)l.u;  break;
	case Oextuw: x = (uint32_t)l.u; break;
	case Ostosi: x = w ? (int64_t)cl->bits.s : (int32_t)cl->bits.s; break;
	case Ostoui: x = w ? (uint64_t)cl->bits.s : (uint32_t)cl->bits.s; break;
	case Odtosi: x = w ? (int64_t)cl->bits.d : (int32_t)cl->bits.d; break;
	case Odtoui: x = w ? (uint64_t)cl->bits.d : (uint32_t)cl->bits.d; break;
	case Ocast:
		x = l.u;
		if (cl->type == CAddr) {
			typ = CAddr;
			sym = cl->sym;
		}
		break;
	default:
		if (Ocmpw <= op && op <= Ocmpl1) {
			if (op <= Ocmpw1) {
				l.u = (int32_t)l.u;
				r.u = (int32_t)r.u;
			} else
				op -= Ocmpl - Ocmpw;
			switch (op - Ocmpw) {
			case Ciule: x = l.u <= r.u; break;
			case Ciult: x = l.u < r.u;  break;
			case Cisle: x = l.s <= r.s; break;
			case Cislt: x = l.s < r.s;  break;
			case Cisgt: x = l.s > r.s;  break;
			case Cisge: x = l.s >= r.s; break;
			case Ciugt: x = l.u > r.u;  break;
			case Ciuge: x = l.u >= r.u; break;
			case Cieq:  x = l.u == r.u; break;
			case Cine:  x = l.u != r.u; break;
			default: die("unreachable");
			}
		}
		else if (Ocmps <= op && op <= Ocmps1) {
			switch (op - Ocmps) {
			case Cfle: x = l.fs <= r.fs; break;
			case Cflt: x = l.fs < r.fs;  break;
			case Cfgt: x = l.fs > r.fs;  break;
			case Cfge: x = l.fs >= r.fs; break;
			case Cfne: x = l.fs != r.fs; break;
			case Cfeq: x = l.fs == r.fs; break;
			case Cfo: x = l.fs < r.fs || l.fs >= r.fs; break;
			case Cfuo: x = !(l.fs < r.fs || l.fs >= r.fs); break;
			default: die("unreachable");
			}
		}
		else if (Ocmpd <= op && op <= Ocmpd1) {
			switch (op - Ocmpd) {
			case Cfle: x = l.fd <= r.fd; break;
			case Cflt: x = l.fd < r.fd;  break;
			case Cfgt: x = l.fd > r.fd;  break;
			case Cfge: x = l.fd >= r.fd; break;
			case Cfne: x = l.fd != r.fd; break;
			case Cfeq: x = l.fd == r.fd; break;
			case Cfo: x = l.fd < r.fd || l.fd >= r.fd; break;
			case Cfuo: x = !(l.fd < r.fd || l.fd >= r.fd); break;
			default: die("unreachable");
			}
		}
		else
			die("unreachable");
	}
	*res = (Con){.type=typ, .sym=sym, .bits={.i=x}};
	return 0;
}

static void
foldflt(Con *res, int op, int w, Con *cl, Con *cr)
{
	float xs, ls, rs;
	double xd, ld, rd;

	if (cl->type != CBits || cr->type != CBits)
		err("invalid address operand for '%s'", optab[op].name);
	*res = (Con){.type = CBits};
	memset(&res->bits, 0, sizeof(res->bits));
	if (w)  {
		ld = cl->bits.d;
		rd = cr->bits.d;
		switch (op) {
		case Oadd: xd = ld + rd; break;
		case Osub: xd = ld - rd; break;
		case Oneg: xd = -ld; break;
		case Odiv: xd = ld / rd; break;
		case Omul: xd = ld * rd; break;
		case Oswtof: xd = (int32_t)cl->bits.i; break;
		case Ouwtof: xd = (uint32_t)cl->bits.i; break;
		case Osltof: xd = (int64_t)cl->bits.i; break;
		case Oultof: xd = (uint64_t)cl->bits.i; break;
		case Oexts: xd = cl->bits.s; break;
		case Ocast: xd = ld; break;
		default: die("unreachable");
		}
		res->bits.d = xd;
		res->flt = 2;
	} else {
		ls = cl->bits.s;
		rs = cr->bits.s;
		switch (op) {
		case Oadd: xs = ls + rs; break;
		case Osub: xs = ls - rs; break;
		case Oneg: xs = -ls; break;
		case Odiv: xs = ls / rs; break;
		case Omul: xs = ls * rs; break;
		case Oswtof: xs = (int32_t)cl->bits.i; break;
		case Ouwtof: xs = (uint32_t)cl->bits.i; break;
		case Osltof: xs = (int64_t)cl->bits.i; break;
		case Oultof: xs = (uint64_t)cl->bits.i; break;
		case Otruncd: xs = cl->bits.d; break;
		case Ocast: xs = ls; break;
		default: die("unreachable");
		}
		res->bits.s = xs;
		res->flt = 1;
	}
}

static Ref
opfold(int op, int cls, Con *cl, Con *cr, Fn *fn)
{
	Ref r;
	Con c;

	if (cls == Kw || cls == Kl) {
		if (foldint(&c, op, cls == Kl, cl, cr))
			return R;
	} else
		foldflt(&c, op, cls == Kd, cl, cr);
	if (!KWIDE(cls))
		c.bits.i &= 0xffffffff;
	r = newcon(&c, fn);
	assert(!(cls == Ks || cls == Kd) || c.flt);
	return r;
}
