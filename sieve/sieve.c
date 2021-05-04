/* Sieve program to search for large values of C(n) where C(n) corresponds
   to OEIS sequence A332580 (http://oeis.org/A332580).

Copyright 2020-2021 Paul Zimmermann, Inria.

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the GNU MPFR Library; see the file COPYING.LIB.  If not, write to
the Free Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston,
MA 02110-1301, USA. */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>
#include <math.h>
#include <gmp.h>
#include <assert.h>
#ifdef NO_OPENMP
#pragma GCC diagnostic ignored "-Wunknown-pragmas"
static int omp_get_thread_num () { return 0; }
static int omp_get_num_threads () { return 1; }
#else
#include <omp.h>
#endif

/* if DIV2=2, divide size of T[] by 2 */
#define DIV2 2

#define UWtype uint64_t
#define UHWtype uint64_t
#define UDItype uint64_t
#define W_TYPE_SIZE 64
#include "longlong.h"

/* with -fast, only sieve primes up to sqrt(B1) */
int fast = 0;

struct prime_info_s {
  unsigned long offset;  /* offset for current primes */
  long current;          /* index of previous prime */
  unsigned int *primes;  /* small primes up to sqrt(p) */
  unsigned long nprimes; /* length of primes[] */
  unsigned char *sieve;  /* sieving table */
  long len;              /* length of sieving table */
  unsigned int *moduli;  /* offset for small primes */
};
typedef struct prime_info_s prime_info[1];

#ifndef ASSERT
#define ASSERT(x)
#endif

void
prime_info_init (prime_info i)
{
  i->offset = 0;
  i->current = -1;
  i->primes = NULL;
  i->nprimes = 0;
  i->sieve = NULL;
  i->len = 0;
  i->moduli = NULL;
}

void
prime_info_clear (prime_info i)
{
  free (i->primes);
  free (i->sieve);
  free (i->moduli);
}

/* this function is thread-safe, provided of course that no two threads
 * tinker with the same prime_info data. */
unsigned long
getprime_mt (prime_info i)
{
  if (i->len)
    {
      unsigned char *ptr = i->sieve + i->current;
      while (!*++ptr);
      i->current = ptr - i->sieve;
    }
  else
    i->current = 0;

  if (i->current < i->len) /* most calls will end here */
    return i->offset + 2 * i->current;

  /* otherwise we have to sieve */
  i->offset += 2 * i->len;

  /* first enlarge sieving table if too small */
  if ((unsigned long) i->len * i->len < i->offset)
    {
      free (i->sieve);
      i->len *= 2;
      i->sieve = (unsigned char *) malloc ((i->len + 1 )
                                           * sizeof (unsigned char));
      /* assume this "small" malloc will not fail in normal usage */
      ASSERT(i->sieve != NULL);
      i->sieve[i->len] = 1; /* End mark */
    }

  /* now enlarge small prime table if too small */
  if ((i->nprimes == 0) ||
      ((unsigned long) i->primes[i->nprimes - 1] * (unsigned long)
       i->primes[i->nprimes - 1] < i->offset + i->len))
      {
	if (i->nprimes == 0) /* initialization */
	  {
	    i->nprimes = 1;
	    i->primes = (unsigned int*) malloc (i->nprimes
                                                * sizeof(unsigned int));
	    /* assume this "small" malloc will not fail in normal usage */
	    ASSERT(i->primes != NULL);
	    i->moduli = (unsigned int*) malloc (i->nprimes
                                                * sizeof(unsigned int));
	    /* assume this "small" malloc will not fail in normal usage */
	    ASSERT(i->moduli != NULL);
	    i->len = 1;
	    i->sieve = (unsigned char *) malloc((i->len + 1) *
                                       sizeof(unsigned char)); /* len=1 here */
	    /* assume this "small" malloc will not fail in normal usage */
	    ASSERT(i->sieve != NULL);
	    i->sieve[i->len] = 1; /* End mark */
	    i->offset = 5;
	    i->sieve[0] = 1; /* corresponding to 5 */
	    i->primes[0] = 3;
	    i->moduli[0] = 1; /* next odd multiple of 3 is 7, i.e. next to 5 */
	    i->current = -1;
	    return 3;
	  }
	else
	  {
	    unsigned int k, p, j, ok;

	    k = i->nprimes;
	    i->nprimes *= 2;
	    i->primes = (unsigned int*) realloc (i->primes, i->nprimes *
                                                 sizeof(unsigned int));
	    i->moduli = (unsigned int*) realloc (i->moduli, i->nprimes *
                                                 sizeof(unsigned int));
	    /* assume those "small" realloc's will not fail in normal usage */
	    ASSERT(i->primes != NULL && i->moduli != NULL);
	    for (p = i->primes[k-1]; k < i->nprimes; k++)
	      {
		/* find next (odd) prime > p */
		do
		  {
		    for (p += 2, ok = 1, j = 0; (ok != 0) && (j < k); j++)
		      ok = p % i->primes[j];
		  }
		while (ok == 0);
		i->primes[k] = p;
		/* moduli[k] is the smallest m such that offset + 2*m = k*p */
		j = i->offset % p;
		j = (j == 0) ? j : p - j; /* -offset mod p */
		if ((j % 2) != 0)
		  j += p; /* ensure j is even */
		i->moduli[k] = j / 2;
	      }
	  }
      }

  /* now sieve for new primes */
  {
    long k;
    unsigned long j, p;
    
    memset (i->sieve, 1, sizeof(unsigned char) * (i->len + 1));
    for (j = 0; j < i->nprimes; j++)
      {
	p = i->primes[j];
	for (k = i->moduli[j]; k < i->len; k += p)
	  i->sieve[k] = 0;
	i->moduli[j] = k - i->len; /* for next sieving array */
      }
  }

  unsigned char *ptr = i->sieve - 1;
  while (!*++ptr);
  i->current = ptr - i->sieve;

  ASSERT(i->current < i->len); /* otherwise we found a prime gap >= sqrt(x)
                                  around x */
  return i->offset + 2 * i->current;
}

static int
ndigits (uint64_t n)
{
  int l = 0;
  while (n != 0)
    {
      l ++;
      n /= 10;
    }
  return l;
}

uint64_t Power10[] = {1UL, 10UL, 100UL, 1000UL, 10000UL, 100000UL, 1000000UL, 10000000UL, 100000000UL, 1000000000UL, 10000000000UL, 100000000000UL, 1000000000000UL, 10000000000000UL, 100000000000000UL, 1000000000000000UL, 10000000000000000UL, 100000000000000000UL, 1000000000000000000UL, 10000000000000000000UL};

static int
nbits (uint64_t e)
{
  int k = 0;
  while (e != 0)
    {
      k++;
      e /= 2;
    }
  return k;
}

/* return a*b mod q, assumes 0 <= a, b < q */
uint64_t
mulmod (uint64_t a, uint64_t b, uint64_t q)
{
  uint64_t h, l, dummy, r;
  umul_ppmm (h, l, a, b);
  udiv_qrnnd (dummy, r, h, l, q);
  return r;
}

/* return a*b mod q, without any assumption on a, b */
uint64_t
mulmod_nonreduced (uint64_t a, uint64_t b, uint64_t q)
{
  uint64_t h, l, dummy, r;
  umul_ppmm (h, l, a, b);
  if (h >= q)
    h = h % q;
  udiv_qrnnd (dummy, r, h, l, q);
  return r;
}

/* return a^e mod m, assuming a < m */
static uint64_t
powmod (uint64_t a, uint64_t e, uint64_t m)
{
  if (e == 0)
    return 1;
  int k = nbits (e);
  k--;
  assert (a < m);
  uint64_t y = a;
  while (k-- > 0)
    {
      y = mulmod (y, y, m);
      if (e & (1UL << k))
        y = mulmod (y, a, m);
    }
  return y;
}

/* assume 0 <= a,b < q */
uint64_t
addmod (uint64_t a, uint64_t b, uint64_t q)
{
  uint64_t c = a + b;
  if (c < a) /* carry: 2^64 <= a+b < 2q which implies q>2^63 */
    return c - q;
  else if (c >= q)
    return c - q;
  else
    return c;
}

/* assume 0 <= a,b < q */
uint64_t
submod (uint64_t a, uint64_t b, uint64_t q)
{
  if (a >= b)
    return a - b;
  else
    return a + q - b;
}

/* compute (X^j-1-j*(X-1))/(X-1)^2 mod q */
uint64_t
compute_z (uint64_t X, uint64_t j, uint64_t q)
{
  mpz_t modulus, Xj, Z;
  uint64_t z;
  mpz_init_set_ui (modulus, X - 1);
  mpz_mul_ui (modulus, modulus, X - 1);
  mpz_mul_ui (modulus, modulus, q);
  mpz_init_set_ui (Xj, X);
  mpz_powm_ui (Xj, Xj, j, modulus);
  mpz_sub_ui (Xj, Xj, 1);
  mpz_init_set_ui (Z, X - 1);
  mpz_mul_ui (Z, Z, j);
  mpz_sub (Z, Xj, Z);
  mpz_divexact_ui (Z, Z, X - 1);
  mpz_divexact_ui (Z, Z, X - 1);
  z = mpz_fdiv_ui (Z, q);
  mpz_clear (Z);
  mpz_clear (Xj);
  mpz_clear (modulus);
  return z;
}

#if 0
/* return 1/a mod m, or zero if non invertible */
static uint64_t
invert (uint64_t a, uint64_t m)
{
  mpz_t t, u;
  uint64_t inv;
  int ret;

  mpz_init_set_ui (t, a);
  mpz_init_set_ui (u, m);
  ret = mpz_invert (t, t, u);
  inv = (ret) ? mpz_get_ui (t) : 0;
  mpz_clear (t);
  mpz_clear (u);
  return inv;
}
#else
static uint64_t
invert (uint64_t a, uint64_t m)
{
  uint64_t m0 = m;
  int64_t x = 1, z = 0;
  /* invariant: a = x*a0 + y*m0, m = z*a0 + t*m0 */
  while (a != 0)
    {
      uint64_t q;
      q = m / a;
      m = m % a;
      /* subtract m -> m - q*a */
      z = z - q * x;
      if (m == 0) /* gcd is a */
        return (a > 1) ? 0 : (x > 0) ? (uint64_t) x : m0 + x;
      q = a / m;
      a = a % m;
      /* subtract a -> a - q*m */
      x = x - q * z;
    }
  /* gcd is m */
  return (m > 1) ? 0 : (z > 0) ? (uint64_t) z : m0 + z;
}
#endif

/* Return the value of n,n+1,...,n+k mod q */
uint64_t
compute_mod (uint64_t n, uint64_t k, uint64_t q)
{
  int l0, l1;
  uint64_t x, y, z, inv = 0;

  l0 = ndigits (n);
  l1 = ndigits (n + k);
  x = 0;
  for (int l = l0; l <= l1; l++)
    {
      uint64_t n0, n1, j, X, Xj, m;
      n0 = (l == l0) ? n : Power10[l-1];
      n1 = (l == l1) ? n+k+1 : Power10[l];
      j = n1 - n0;
      X = Power10[l] % q;
      /* if X=0 or X=1, we don't need inv */
      if (X > 1)
        inv = invert (X - 1, q);
      Xj = powmod (X, j, q);
      x = mulmod (x, Xj, q);
      /* put in y the contribution of n0,n0,...,n0 */
      if (X == 0)
        y = 1;
      else if (X == 1)
        y = j;
      else if (inv)
        {
          y = Xj;
          y = submod (y, 1, q);
          y = mulmod (y, inv, q);
        }
      else if (X-1 <= ULONG_MAX / q)
        {
          m = q * (X-1);
          y = powmod (X, j, m);
          y = submod (y, 1, m);
          assert (y % (X-1) == 0);
          y = y / (X-1);
        }
      else /* rare case */
        {
          mpz_t mz, yz;
          mpz_init_set_ui (mz, q);
          mpz_mul_ui (mz, mz, X-1);
          mpz_init_set_ui (yz, X);
          mpz_powm_ui (yz, yz, j, mz);
          mpz_sub_ui (yz, yz, 1);
          mpz_mod (yz, yz, mz);
          assert (mpz_divisible_ui_p (yz, X-1));
          mpz_divexact_ui (yz, yz, X-1);
          assert (mpz_fits_ulong_p (yz));
          y = mpz_get_ui (yz);
          mpz_clear (yz);
          mpz_clear (mz);
        }
      y = mulmod_nonreduced (n0, y, q);
      /* put in z the contribution of 0,1,2,...,j-1 */
      if (X == 0)
        z = j - 1;
      else if (X == 1)
        {
          if (j % 2 == 0)
            z = mulmod_nonreduced (j/2, j-1, q);
          else
            z = mulmod_nonreduced (j, (j-1)/2, q);
        }
      else if (inv)
        {
          uint64_t inv2 = mulmod (inv, inv, q);
          z = powmod (X, j, q);
          z = submod (z, 1, q);
          uint64_t t = mulmod_nonreduced (j, X-1, q);
          z = submod (z, t, q);
          z = mulmod (z, inv2, q);
        }
      else
        {
          assert (X > 0);
          if (X - 1 > ULONG_MAX / q)
            z = compute_z (X, j, q);
          else
            {
              m = q * (X-1);
              if (X - 1 > ULONG_MAX / m)
                z = compute_z (X, j, q);
              else
                {
                  m = m * (X-1);
                  z = powmod (X, j, m);
                  z = submod (z, 1, m);
                  uint64_t t = mulmod_nonreduced (j, X-1, m);
                  z = submod (z, t, m);
                  assert (z % ((X-1)*(X-1)) == 0);
                  z = z / ((X-1)*(X-1));
                  z = z % q;
                }
            }
        }
      x = addmod (x, y, q);
      x = addmod (x, z, q);
    }
  return x;
}

int
isprime (uint64_t n)
{
  if (n % 2 == 0)
    return n == 2;
  for (uint64_t p = 3; p <= n / p; p += 2)
    if (n % p == 0)
      return 0;
  return 1;
}

/* Return the multiplicative order of x mod q.
   See https://rosettacode.org/wiki/Multiplicative_order.
   Assumes q = p^e for some exponent e >= 1, where p is an odd prime. */
uint64_t
Order (uint64_t x, uint64_t q, uint64_t p)
{
  assert (x < q);
  if (x == 1)
    return 1;
  uint64_t gmax = q - 1, e, y;
  gmax = (q / p) * (p - 1);
  uint64_t r = gmax; /* unfactored part of gmax */

  /* we do not need p any more, so we reuse it */
  for (p = 2; p <= r / p; p += 1 + (p > 2))
      if (r % p == 0)
        {
          e = 0;
          while (r % p == 0)
            {
              e ++;
              r = r / p;
              gmax = gmax / p;
            }
          y = powmod (x, gmax, q);
          while (y != 1)
            {
              gmax *= p;
              y = powmod (y, p, q);
            }
        }
  /* now r = 1 or r is prime */
  if (r > 1)
    {
      p = r;
      gmax = gmax / p;
      y = powmod (x, gmax, q);
      if (y != 1)
        gmax *= p;
    }
  return gmax;
}

typedef struct {
  uint64_t r; /* g^j mod q */
  uint64_t j; /* j */
} pair_t;

int
cmp_pair (const void *a, const void *b)
{
  const pair_t *u = a;
  const pair_t *v = b;
  if (u->r < v->r || (u->r == v->r && u->j < v->j))
    return -1;
  else
    return 1;
}


/* Return 0 <= i < o, such that g^i = h, or if no such i exists, return o. */
uint64_t
solve_dlp (uint64_t g, uint64_t h, uint64_t q, uint64_t o)
{
#define DLP_THRESHOLD 16
  if (o < DLP_THRESHOLD)
    {
      uint64_t x = g;
      for (uint64_t i = 1; i < o; i++)
        {
          /* Invariant: x = g^i mod q */
          if (x == h)
            return i;
          x = mulmod (x, g, q);
        }
      return o;
    }

  /* use a baby-step, giant-step approach: let t = ceil(sqrt(min(o,q))),
     precompute a[j]=g^j mod q for 0 <= j < t, then compute b[k]=h/g^(t*k)
     for 0 <= k < t, and try to find a[j]=b[k], in which case i=t*k+j is a
     solution. */
  uint64_t t = ceil (sqrt ((double) (o <= q) ? o : q));
  pair_t *a = malloc ((t + 1) * sizeof (pair_t));
  a[0].r = 1;
  a[0].j = 0;
  for (uint64_t j = 1; j < t; j++)
    {
      a[j].r = mulmod (a[j-1].r, g, q);
      if (a[j].r == h)
        {
          o = j;
          goto end;
        }
      a[j].j = j;
    }
  /* sort */
  qsort (a, t, sizeof (pair_t), cmp_pair);
  a[t].r = q; /* sentinel */
  uint64_t b = h;
  uint64_t gt = powmod (g, t, q);
  uint64_t invgt = invert (gt, q);
  for (uint64_t k = 1; k < t; k++)
    {
      b = mulmod (b, invgt, q);
      /* search by dichotomy */
      uint64_t u = 0, v = t, w;
      assert (b < a[v].r);
      /* invariant: a[u].r <= b < a[v].r, except maybe if b < a[0].r */
      while (u + 1 < v)
        {
          w = u + (v - u) / 2; /* avoids overflow in (u+v)/2 */
          if (b < a[w].r)
            v = w;
          else /* a[w].r <= b */
            u = w;
        }
      if (a[u].r == b)
        {
          o = t * k + a[u].j;
          break;
        }
    }
 end:
  free (a);
  return o;
}

#if 0
/* Return 0 <= i < o, such that g^i = h, or if no such i exists, return o. */
uint64_t
solve_dlp_ref (uint64_t g, uint64_t h, uint64_t q, uint64_t o)
{
  if (o < DLP_THRESHOLD)
    {
      uint64_t x = g;
      for (uint64_t i = 1; i < DLP_THRESHOLD; i++)
        {
          /* Invariant: x = g^i mod q */
          if (x == h)
            return i;
          x = mulmod (x, g, q);
        }
      return o;
    }

  /* use a baby-step, giant-step approach: let t = ceil(sqrt(min(o,q))),
     precompute a[j]=g^j mod q and b[k]=h/g^(t*k) for 0 <= j,k < t,
     and try to find a[j]=b[k], in which case i=j+t*k is a solution. */
  uint64_t t = ceil (sqrt ((double) (o <= q) ? o : q));
  uint64_t i = o;
  uint64_t *a = malloc (t * sizeof (uint64_t));
  uint64_t *b = malloc (t * sizeof (uint64_t));
  a[0] = 1;
  for (uint64_t j = 1; j < t; j++)
    {
      a[j] = mulmod (a[j-1], g, q);
      if (a[j] == h)
        {
          i = j;
          goto end;
        }
    }
  b[0] = h;
  uint64_t gt = powmod (g, t, q);
  uint64_t invgt = invert (gt, q);
  for (uint64_t k = 1; k < t; k++)
    b[k] = mulmod (b[k-1], invgt, q);
  /* try to find a match */
  for (uint64_t k = 0; k < t; k++)
    for (uint64_t j = 0; j < t; j++)
      if (a[j] == b[k])
        {
          i = j + k * t;
          goto end;
        }
 end:
  free (a);
  free (b);
  return i;
}
#endif

// #define TRACE_k 259110640

/* easy case, where p does not divide 10^l-1 */
void
sieve_p_easy (unsigned char *T, uint64_t n, int l, uint64_t B0, uint64_t B1,
              uint64_t p, uint64_t Pbound, double logB)
{
  int emax = 1;
  uint64_t q = p;

  while (q <= Pbound / p)
    {
      q *= p;
      emax ++;
    }
  int logsum = 0;
  double logp = log ((double) p) / logB;
  q = 1;
  for (int e = 1; e <= emax; e++)
    {
      q *= p;
      uint64_t n0 = ((B0 + q) / q) * q - 1; /* ceil((B0+1)/q)*q-1 */
      if (n0 >= B1)
        break; /* no number in [B0,B1[ is divisible by q=p^e, nor
                  by larger powers of p */
      /* ensure n0 is even */
      if ((n0 % 2) == 1)
        {
          n0 += q;
          if (n0 >= B1)
            break;
        }
      int logq = ceil (e * logp - logsum);
      logsum += logq;
      uint64_t x = compute_mod (n, n0 - n, q);
      uint64_t z = 0;
      uint64_t t = 1 + (B1 - n0 - 1) / q;
      uint64_t X = Power10[l] % q;
      uint64_t Xq = powmod (X, q, q);
      uint64_t inv = (X == 0) ? q-1 : invert (X-1, q);
      /* Y is zero since it is (n0+1)*(X^q-1)/(X-1) mod q, and n0+1 = 0 mod q */
      if (X == 0)
        z = q - 1;
      uint64_t oneinv2, inv2;
      inv2 = mulmod (inv, inv, q);   /* 1/(X-1)^2 mod q */
      oneinv2 = inv2;
      z = oneinv2;
      uint64_t shift = (X == 0) ? 0 : oneinv2;
      /* The real value of z should be z-shift, thus instead of comparing
         U t0 0, we compare to shift. */
      uint64_t v0 = shift;
      if (X > 0)
        x = addmod (x, z, q);
      else /* for X=0, z is invariant */
        v0 = submod (v0, z, q);
      uint64_t x0 = x;
      /* We want x0*Xq^i = v0 mod q, thus Xq^i = v0/x0 mod q.
         If g is the multiplicative order of Xq modulo q,
         and i0 is the first solution, we can have only one
         solution 0 <= i < g, since if we have another solution i0 < j0 < g,
         then Xq^(j0-i0) = 1 mod q, thus the order would not be minimal.
         Note: assume the multiplicative order of Xq is a, and that of
         v0/x0 is b: Xq^a = 1 mod q, and (v0/x0)^b = 1 mod q.
         This implies Xq^(a*i) = 1 = (v0/x0)^a, thus b divides a. */

      /* If x0 = 0 there is no solution (necessarily v0 <> 0, otherwise
         all values would be solutions). Same if Xq = 0. */
      if (x0 == 0)
        return;
      if (Xq == 0)
        return;
      assert (v0 != 0);

      uint64_t t0 = invert (x0, q);
      assert (t0 != 0);
      t0 = mulmod (v0, t0, q); /* v0/x0 mod q */

      /* we have ensured n0 is even */
      assert ((n0 % 2) == 0);

      /* we want Xq^i = t0 mod q for 0 <= i < t */
      assert (t > 0);
      if (t < DLP_THRESHOLD)
        {
          x = 1;
          /* we should ensure n0 + q * i even: since n0 is even and q is odd,
             this implies i is even */
          Xq = mulmod (Xq, Xq, q);
          for (uint64_t i = 0; i < t; i+=2)
            {
              if (x == t0)
                {
#ifdef TRACE_k
                  if (n0+q*i == TRACE_k + n)
                    printf ("%lu divisible by %lu: add %u (now %u)\n",
                            n0+q*i-n, q, logq, T[(n0 + q * i - B0) / DIV2] + logq);
#endif
#pragma omp atomic update
                  T[(n0 + q * i - B0) / DIV2] += logq;
                }
              x = mulmod (x, Xq, q);
            }
          return;
        }

      uint64_t i0 = solve_dlp (Xq, t0, q, t);
      if (i0 == t) /* no solution to Xq^i = t0 mod q for 0 <= i < t */
        return;

      uint64_t order = Order (Xq, q, p);

        /* we should ensure n0 + i * q is even, since n0 is even, and q odd,
           this implies i is even, where i = i0 + j*order */
        if ((i0 % 2) == 1) /* i0 is odd */
          {
            if ((order % 2) == 0) /* there can be no even value of n0 + q*i */
              return;
            i0 += order; /* now i0 is even */
          }
        /* now n0 + q * i0 is even */
        assert (((n0 + q * i0) % 2) == 0);
        if ((order % 2) == 1)
	      order *= 2;
      for (uint64_t i = i0; i < t; i += order)
        {
          /* k = B0 + DIV2 * i - n thus i = (n + k - B0) / DIV2 */
#ifdef TRACE_k
          if (n0+q*i == TRACE_k + n)
            printf ("%lu divisible by %lu: add %u (now %u)\n",
                    n0+q*i-n, q, logq, T[(n0 + q * i - B0) / DIV2] + logq);
#endif
#pragma omp atomic update
          T[(n0 + q * i - B0) / DIV2] += logq;
        }
    }
}

void
sieve_p (unsigned char *T, uint64_t n, int l, uint64_t B0, uint64_t B1,
         uint64_t p, uint64_t Pbound, double logB)
{
  if (Power10[l] % p != 1)
    return sieve_p_easy (T, n, l, B0, B1, p, Pbound, logB);

  int emax = 1;
  uint64_t q = p;

  while (q <= Pbound / p)
    {
      q *= p;
      emax ++;
    }
  int logsum = 0;
  double logp = log ((double) p) / logB;
  q = 1;
  for (int e = 1; e <= emax; e++)
    {
      q *= p;
      uint64_t n0 = ((B0 + q) / q) * q - 1; /* ceil((B0+1)/q)*q-1 */
      if (n0 >= B1)
        break; /* no number in [B0,B1[ is divisible by q=p^e, nor
                  by larger powers of p */
      int logq = ceil (e * logp - logsum);
      logsum += logq;
      uint64_t x = compute_mod (n, n0 - n, q);
      uint64_t t = 1 + (B1 - n0 - 1) / q;
      /* alpha = (X^q-1)/(X-1): checked by exhaustive search that for
         X <= 10^19, for all prime divisors p of X-1, and all q=p^e <= X,
         then alpha is 0 mod q, and z is always 0.
         Same for y, since y = (n0+1)*alpha.
         Also checked by exhaustive search that Xq=1, thus:
         * either x <> 0, and no value is divisible by q
           (this happens for n=4 and k=6838)
         * or x=0, and all values are divisible by q. */
      if (x != 0)
        return;
      /* we should ensure n0 + q * i is even */
      int i0 = 0;
      if (((n0 + q * i0) % 2) == 1) /* n0 + q * i0 is odd */
        i0 ++;
      assert (((n0 + q * i0) % 2) == 0);
      for (uint64_t i = i0; i < t; i += 2)
        {
#ifdef TRACE_k
          if (n0+q*i-n == TRACE_k)
            printf ("%lu divisible by %lu: add %u (now %u)\n",
                    n0+q*i-n, q, logq, T[(n0 + q * i - B0) / DIV2] + logq);
#endif
#pragma omp atomic update
          T[(n0 + q * i - B0) / DIV2] += logq;
        }
    }
}

/* pi is shared among all threads */
void
doit (unsigned char *T, uint64_t n, int l, uint64_t B0, uint64_t B1,
      uint64_t Pbound, double logB, prime_info pi)
{
  int tid;
  uint64_t p = 0, lastp = 0;
  tid = omp_get_thread_num ();
#define NPOOL 128
  uint64_t pool[NPOOL];
  while (p <= Pbound)
    {
#pragma omp critical
      {
	for (int i = 0; i < NPOOL; i++)
	  pool[i] = getprime_mt (pi);
      }
      for (int i = 0; i < NPOOL; i++)
	{
	  p = pool[i];
	  if (p > Pbound)
	    break;
	  lastp = p;
	  sieve_p (T, n, l, B0, B1, p, Pbound, logB);
	}
    }
#ifndef TRACE_k
  printf ("thread %i is done, last prime %llu\n", tid,
          (unsigned long long) lastp);
  fflush (stdout);
#endif
}

void
parallel_memset (void *s, int c, size_t n)
{
  int nthreads;
#pragma omp parallel
  nthreads = omp_get_num_threads ();
  size_t h = (n + nthreads - 1) / nthreads;
#pragma omp parallel for schedule(static,1)
  for (int i = 0; i < nthreads; i++)
    {
      int tid = omp_get_thread_num ();
      size_t n0 = tid * h;
      if (n0 < n)
        memset (s + n0, c, (h < n - n0) ? h : n - n0);
    }
}

void
sieve (uint64_t n, uint64_t kmax, uint64_t Pbound, uint64_t n0)
{
  int nthreads;
#pragma omp parallel
  nthreads = omp_get_num_threads ();
  printf ("Using %d thread(s)\n", nthreads);
  int l = ndigits (n + kmax);
  uint64_t B0;
  B0 = (n0 == 0) ? Power10[l-1] : n0;
  uint64_t B1 = n + kmax + 1;
  assert (ndigits (B0) == l);
  /* ensure B0,B1 are even */
  if (B0 & 1)
    B0 --; /* will not change decade of B0 */
  if (B1 & 1)
    B1 ++;
  assert (ndigits (B0) == ndigits (B1-1)); /* we sieve up to B1-1 */
  uint64_t m = B1 - B0;
  assert ((m % DIV2) == 0);
  unsigned char *T = malloc ((m / DIV2) * sizeof (char));
  assert (T != NULL);
  uint64_t sqrtB1 = sqrt ((double) B1);
  if (Pbound == 0)
    {
      Pbound = (fast == 0) ? B1 : (uint64_t) sqrtB1;
      printf ("Using bound=%llu\n", (unsigned long long) Pbound);
    }
  parallel_memset (T, 0, (m / DIV2) * sizeof (char));
  uint64_t q, p;
  q = 1;
  p = 3;
  int bound = 256;
  while (q <= B1 / p)
    {
      q *= p;
      do p ++; while (isprime (p) == 0);
      bound --;
    }
  double logB = log ((double) B1) / bound;
  // printf ("logB=%f\n", logB);
  bound = floor (log ((double) B0) / logB);
  printf ("Sieve n=%llu %llu-%llu...\n", (unsigned long long) n,
          (unsigned long long) B0, (unsigned long long) B1-1);
  fflush (stdout);
  prime_info pi;
  prime_info_init (pi);
#pragma omp parallel for schedule(static,1)
  for (int i = 0; i < nthreads; i++)
    doit (T, n, l, B0, B1, Pbound, logB, pi);
  prime_info_clear (pi);

  /* find large values of T[i] */
#ifdef TRACE_k
  printf ("bound=%d T[k]=%u %lu\n", bound, T[(n + TRACE_k - B0) / DIV2],
          (n + TRACE_k - B0) / DIV2);
  fflush (stdout);
#endif
  printf ("Scan sieve array...\n");
  uint64_t nsols = 0;
  /* only need to check entries where B0 + i is even, thus i even since B0 is even */
#pragma omp parallel for
  for (uint64_t i = 0; i < m / DIV2; i++)
    if (T[i] >= bound)
      {
        int bound2 = floor (log ((double) (B0 + i)) / logB);
#ifdef TRACE_k
        if (i == (n + TRACE_k - B0) / DIV2)
          printf ("bound2=%d T[k]=%u\n", bound2, T[i]);
#endif
        if (T[i] >= bound2)
#pragma omp critical
          {
            printf ("###### %llu: %d\n",
                    (unsigned long long) B0 + DIV2 * i - n, T[i]);
            fflush (stdout);
            nsols ++;
          }
      }
  free (T);
  printf ("Found %llu solution(s)\n", (unsigned long long) nsols);
}

int
main (int argc, char *argv[])
{
  uint64_t n, nmax, Pbound = 0, n0 = 0;

  while (argc >= 2 && argv[1][0] == '-')
    {
      if (argc >= 2 && strcmp (argv[1], "-fast") == 0)
        {
          fast = 1;
          argc --;
          argv ++;
        }
      else if (argc >= 3 && strcmp (argv[1], "-bound") == 0)
        {
          Pbound = strtoul (argv[2], NULL, 10);
          argc -= 2;
          argv += 2;
        }
      else if (argc >= 3 && strcmp (argv[1], "-n0") == 0)
        {
          n0 = strtoul (argv[2], NULL, 10);
          argc -= 2;
          argv += 2;
        }
      else
        {
          fprintf (stderr, "Unknown option: %s\n", argv[1]);
          exit (EXIT_FAILURE);
        }
    }

  if (argc != 3)
    {
      fprintf (stderr, "Usage: %s [-fast] n nmax\n", argv[0]);
      exit (EXIT_FAILURE);
    }
  n = strtoul (argv[1], NULL, 10);
  nmax = strtoul (argv[2], NULL, 10);

  printf ("DLP_THRESHOLD=%d\n", DLP_THRESHOLD);

  uint64_t kmax = nmax - n;
  sieve (n, kmax, Pbound, n0);

  return 0;
}
