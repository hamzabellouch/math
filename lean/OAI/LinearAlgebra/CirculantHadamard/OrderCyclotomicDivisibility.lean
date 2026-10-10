import OAI.LinearAlgebra.CirculantHadamard.IntegerLocalDivisibility
import OAI.LinearAlgebra.CirculantHadamard.IntegerTwoLocal
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicIntegerEvaluation
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicRemainder
import OAI.LinearAlgebra.CirculantHadamard.DyadicRemainder
import OAI.LinearAlgebra.CirculantHadamard.RamifiedLocal

namespace OAI

universe uA

/-!
# Dyadic divisibility of opposite coefficient differences

We evaluate the actual integer cyclic group ring in the cyclotomic extension
of the integers localized at two. The norm identity forces divisibility in
that DVR. Its free monic presentation then transfers this divisibility to the
paired coefficient differences, and localization reflects it to the integers.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

/-- The canonical polynomial with the literal integer coefficients of a cyclic
element evaluates to the same element in the cyclotomic quotient. -/
theorem integerCyclotomicEvaluation_coefficientPolynomial
    (A : Type uA) [CommRing A] (n : ℕ) [NeZero n] (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      AdjoinRoot.mk (cyclotomic n A)
        (DyadicRemainder.coefficientPolynomial n
          (fun i => algebraMap ℤ A (T.coeff (i : ZMod n)))) := by
  classical
  rw [integerCyclotomicEvaluation_apply]
  simp only [DyadicRemainder.coefficientPolynomial, map_sum,
    ← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
    algebraMap_int_eq, Int.coe_castRingHom, map_intCast]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ a : Fin (n + 1), (T.coeff a : AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val) =
        ∑ a : Fin (n + 1), (T.coeff (Fin.ofNat (n + 1) a.val) :
          AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val
      simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]

/-- A scalar norm of the stated dyadic size forces each opposite coefficient
difference to be divisible by its square-root dyadic factor. No condition on
the parity of the coefficients, or separate positivity of `u`, is required. -/
theorem dyadic_difference_dvd (k t u : ℕ)
    (T : CyclicRing.Elem ℤ (2 ^ (k + 1))) (hu : Odd u)
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∀ j : ZMod (2 ^ k), (2 : ℤ) ^ t ∣
      T.coeff (j.val : ZMod (2 ^ (k + 1))) -
        T.coeff ((j.val + 2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
  let A := IntegerTwoLocal.Ring
  let S := RamifiedLocal.Extension A 2 k
  let : IsDomain S := RamifiedLocal.isDomain A Nat.prime_two k
    IntegerTwoLocal.maximalIdeal_eq_span
  let : IsLocalRing S := RamifiedLocal.isLocalRing A Nat.prime_two k
    IntegerTwoLocal.maximalIdeal_eq_span
  let : IsDiscreteValuationRing S := RamifiedLocal.isDiscreteValuationRing A
    Nat.prime_two k IntegerTwoLocal.maximalIdeal_eq_span
  let : CharZero S := charZero_of_injective_algebraMap
    (RamifiedLocal.algebraMap_injective A Nat.prime_two k)
  have hn : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
  let : NeZero (2 ^ (k + 1)) := ⟨hn.ne'⟩
  let x : S := integerCyclotomicEvaluation A (2 ^ (k + 1)) T
  have huS : IsUnit ((u : S) ^ 2) := by
    have hunit := (IntegerTwoLocal.isUnit_natCast_of_odd u hu).map
      (algebraMap A S)
    have huS' : IsUnit (u : S) := by simpa only [map_natCast] using hunit
    exact huS'.pow 2
  have hnormS : x * RamifiedConjugation.cyclotomicConjugation A (2 ^ (k + 1)) hn x =
      (2 : S) ^ (2 * t) * (u : S) ^ 2 := by
    have hcast : (((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) : S) =
        (2 : S) ^ (2 * t) * (u : S) ^ 2 := by
      exact (Int.cast_natCast (R := S) (2 ^ (2 * t) * u ^ 2)).trans
        (show ((2 ^ (2 * t) * u ^ 2 : ℕ) : S) =
            (2 : S) ^ (2 * t) * (u : S) ^ 2 by
          exact (Nat.cast_mul (α := S) (2 ^ (2 * t)) (u ^ 2)).trans
            (congrArg₂ (fun a b : S => a * b)
              ((Nat.cast_pow (α := S) 2 (2 * t)).trans
                (congrArg (fun a : S => a ^ (2 * t)) (Nat.cast_two (R := S))))
              (Nat.cast_pow (α := S) u 2)))
    exact (integerCyclotomicEvaluation_norm A (2 ^ (k + 1)) hn T
      ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) hnorm).trans hcast
  have hdiv : (2 : S) ^ t ∣ x :=
    RamifiedConjugation.cyclotomic_pow_dvd_of_norm_eq A (2 ^ (k + 1)) hn
      2 x ((u : S) ^ 2) t huS hnormS
  let c : ℕ → A := fun i => algebraMap ℤ A (T.coeff (i : ZMod (2 ^ (k + 1))))
  have hpoly : algebraMap A S ((2 : A) ^ t) ∣
      AdjoinRoot.mk (cyclotomic (2 ^ (k + 1)) A)
        (DyadicRemainder.coefficientPolynomial (2 ^ (k + 1)) c) := by
    simpa only [x, map_pow, map_ofNat,
      integerCyclotomicEvaluation_coefficientPolynomial, c,
      eq_intCast] using hdiv
  intro j
  have hcoeff := CyclotomicRemainder.adjoinRoot_dvd_coeff_modByMonic
    (cyclotomic (2 ^ (k + 1)) A) (cyclotomic.monic _ _) ((2 : A) ^ t)
    (DyadicRemainder.coefficientPolynomial (2 ^ (k + 1)) c) hpoly j.val
  rw [DyadicRemainder.coefficientPolynomial_modByMonic_cyclotomic,
    DyadicRemainder.remainder_coeff _ _ _ j.val_lt] at hcoeff
  apply integer_prime_pow_dvd_of_localization (A := A) (P := IntegerTwoLocal.ideal)
    Nat.prime_two rfl t
  simpa only [c, map_sub, Nat.cast_ofNat] using hcoeff

end CirculantHadamard

end

end OAI
