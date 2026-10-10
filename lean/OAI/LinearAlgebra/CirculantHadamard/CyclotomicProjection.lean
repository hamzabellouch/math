import OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial
import OAI.LinearAlgebra.CirculantHadamard.CyclicProjectionPolynomial
import OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluationAt
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicRemainder
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace OAI

universe uR uS

/-!
# Integral division after projection to a smaller cyclic group

At an element of order dividing `p ^ e`, the prime-power cyclotomic polynomial
`cyclotomic (p ^ (e + 1)) R` evaluates to the scalar `p`. Consequently, if all
coefficients of a polynomial's monic remainder are divisible by `p`, its image
in the group algebra of `ZMod (p ^ e)` is divisible by the same scalar.

All divisions are witnessed inside the coefficient ring or group algebra.
No domain instance or cancellation assumption on a finite group algebra is used.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- Every actual cyclic group-ring element has a polynomial representative. -/
theorem exists_cyclic_polynomial (n : ℕ) [NeZero n]
    (F : AddMonoidAlgebra R (ZMod n)) :
    ∃ P : R[X], aeval (CyclicPolynomial.generator R n) P = F := by
  obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective (CyclicPolynomial.cyclicEquiv R n F)
  refine ⟨P, ?_⟩
  apply (CyclicPolynomial.cyclicEquiv R n).injective
  rw [CyclicPolynomial.cyclicEquiv_aeval, hP]

/-- The actual root in the cyclotomic quotient satisfies its `n`th-power
relation, directly because the cyclotomic polynomial divides `X ^ n - 1`. -/
theorem cyclotomicAdjoinRoot_pow (n : ℕ) :
    AdjoinRoot.root (cyclotomic n R) ^ n = 1 := by
  have h : AdjoinRoot.mk (cyclotomic n R) ((X : R[X]) ^ n - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one n R)
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] using h

/-- Evaluation of the actual cyclic group ring at the root in its cyclotomic
quotient, using the root's proved power relation. -/
def cyclicCyclotomicEvaluation (R : Type uR) [CommRing R] (n : ℕ) [NeZero n] :
    AddMonoidAlgebra R (ZMod n) →ₐ[R] AdjoinRoot (cyclotomic n R) :=
  CyclicRing.evaluateAt n (AdjoinRoot.root (cyclotomic n R))
    (cyclotomicAdjoinRoot_pow n)

@[simp]
theorem cyclicCyclotomicEvaluation_aeval (n : ℕ) [NeZero n] (P : R[X]) :
    cyclicCyclotomicEvaluation R n (aeval (CyclicPolynomial.generator R n) P) =
      AdjoinRoot.mk (cyclotomic n R) P := by
  rw [cyclicCyclotomicEvaluation, CyclicRing.evaluateAt_aeval, AdjoinRoot.aeval_eq]

/-- A prime-power cyclotomic polynomial becomes `p` at every element whose
`p ^ e`th power is one. -/
theorem aeval_cyclotomic_prime_pow_of_pow_eq_one {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) :
    aeval x (cyclotomic (p ^ (e + 1)) R) = (p : S) := by
  rw [cyclotomic_prime_pow_eq_geom_sum hp]
  simp [hx]

/-- Evaluating a monic division identity preserves integral divisibility if
both the divisor's evaluation and the remainder have the stated scalar factor. -/
theorem aeval_divisible_of_modByMonic_coeff (x : S) (F Q : R[X]) (a : R)
    (_hQ : Q.Monic) (hQx : aeval x Q = algebraMap R S a)
    (hcoeff : ∀ i, a ∣ (F %ₘ Q).coeff i) :
    ∃ G : S, aeval x F = algebraMap R S a * G := by
  obtain ⟨T, hT⟩ := (C_dvd_iff_dvd_coeff a (F %ₘ Q)).2 hcoeff
  refine ⟨aeval x T + aeval x (F /ₘ Q), ?_⟩
  calc
    aeval x F = aeval x (F %ₘ Q) + aeval x Q * aeval x (F /ₘ Q) := by
      rw [← map_mul, ← map_add, modByMonic_add_div F Q]
    _ = algebraMap R S a * (aeval x T + aeval x (F /ₘ Q)) := by
      rw [hT, map_mul, aeval_C, hQx, mul_add]

/-- Integral divisibility at a `p ^ e`th root follows from coefficientwise
divisibility of the remainder modulo the next cyclotomic polynomial. -/
theorem aeval_divisible_of_cyclotomic_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : S, aeval x F = (p : S) * G := by
  have hQx : aeval x (cyclotomic (p ^ (e + 1)) R) =
      algebraMap R S (p : R) := by
    simpa only [map_natCast] using aeval_cyclotomic_prime_pow_of_pow_eq_one hp x hx
  simpa only [map_natCast] using aeval_divisible_of_modByMonic_coeff x F
    (cyclotomic (p ^ (e + 1)) R) (p : R) (cyclotomic.monic _ _) hQx hcoeff

/-- The concrete `p`-division step in the cyclic group algebra: project from
order `p ^ (e + 1)` to order `p ^ e`, then divide integrally by `p`. -/
theorem cyclicProjection_divisible_of_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e))
          (aeval (CyclicPolynomial.generator R (p ^ (e + 1))) F) =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  rw [cyclicProjection_aeval]
  exact aeval_divisible_of_cyclotomic_remainder_coeff hp
    (CyclicPolynomial.generator R (p ^ e)) (CyclicPolynomial.generator_pow R (p ^ e))
    F hcoeff

/-- Divisibility at the actual primitive-root quotient forces integral
divisibility after projecting the actual cyclic group-ring element.

The concrete monic quotient's linear remainder map supplies coefficientwise
divisibility of the remainder. -/
theorem cyclicProjection_divisible_of_cyclotomicEvaluation {p e : ℕ}
    [NeZero p] (hp : p.Prime) (F : AddMonoidAlgebra R (ZMod (p ^ (e + 1))))
    (hdiv : (p : AdjoinRoot (cyclotomic (p ^ (e + 1)) R)) ∣
      cyclicCyclotomicEvaluation R (p ^ (e + 1)) F) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e)) F =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  obtain ⟨P, rfl⟩ := exists_cyclic_polynomial (p ^ (e + 1)) F
  rw [cyclicCyclotomicEvaluation_aeval] at hdiv
  apply cyclicProjection_divisible_of_remainder_coeff hp P
  intro i
  exact CyclotomicRemainder.adjoinRoot_dvd_coeff_modByMonic
    (cyclotomic (p ^ (e + 1)) R) (cyclotomic.monic _ _) (p : R) P
    (by simpa only [map_natCast] using hdiv) i

end CirculantHadamard

end

end OAI
