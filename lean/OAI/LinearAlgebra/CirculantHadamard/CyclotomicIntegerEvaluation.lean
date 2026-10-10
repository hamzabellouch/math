import OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluation
import OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial
import OAI.LinearAlgebra.CirculantHadamard.RamifiedConjugation

namespace OAI

universe uA

/-!
# Integer cyclic evaluation and actual cyclotomic conjugation

The coefficient map is the integer cast into the cyclotomic quotient. The
character sends the cyclic generator to its adjoined root. The root-inverting
automorphism therefore carries evaluation to evaluation of the actual cyclic
group-ring involution.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]

/-- Integer cyclic group-ring evaluation in the actual cyclotomic quotient. -/
def integerCyclotomicEvaluation :
    CyclicRing.Elem ℤ n →+* AdjoinRoot (cyclotomic n A) :=
  CyclicRing.evaluate (Int.castRingHom (AdjoinRoot (cyclotomic n A)))
    (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
      (RamifiedConjugation.root_pow_order A n))

theorem integerCyclotomicEvaluation_apply (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      ∑ a : ZMod n, (T.coeff a : AdjoinRoot (cyclotomic n A)) *
        AdjoinRoot.root (cyclotomic n A) ^ a.val := by
  rw [integerCyclotomicEvaluation, CyclicRing.evaluate_apply]
  rfl

@[simp] theorem integerCyclotomicEvaluation_scalar (a : ℤ) :
    integerCyclotomicEvaluation A n (CyclicRing.scalar n a) =
      (a : AdjoinRoot (cyclotomic n A)) :=
  CyclicRing.evaluate_scalar _ _ a

variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]

/-- The actual character intertwines negation of its index and the proved
cyclotomic conjugation. -/
theorem cyclotomicPowerCharacter_neg (a : ZMod n) :
    CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
        (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd (-a)) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
          (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd a)) := by
  let χ := CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
    (RamifiedConjugation.root_pow_order A n)
  have hnonzero : χ (Multiplicative.ofAdd a) ≠ 0 :=
    pow_ne_zero a.val
      ((RamifiedConjugation.root_isPrimitiveRoot A n hn).isUnit (ne_of_gt hn)).ne_zero
  apply mul_right_cancel₀ hnonzero
  have hleft : χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) = 1 := by
    rw [← map_mul]
    change χ (Multiplicative.ofAdd (-a + a)) = 1
    simp
  change χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) =
    RamifiedConjugation.cyclotomicConjugation A n hn
      (χ (Multiplicative.ofAdd a)) * χ (Multiplicative.ofAdd a)
  rw [hleft]
  symm
  change RamifiedConjugation.cyclotomicConjugation A n hn
      (AdjoinRoot.root (cyclotomic n A) ^ a.val) *
    AdjoinRoot.root (cyclotomic n A) ^ a.val = 1
  rw [map_pow, RamifiedConjugation.cyclotomicConjugation_root, ← mul_pow,
    RamifiedConjugation.root_pow_pred_mul_root A n hn, one_pow]

/-- Evaluating the integer cyclic involution is exactly the cyclotomic
conjugate of the evaluated element. -/
theorem integerCyclotomicEvaluation_ringStar (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n (CyclicRing.ringStar T) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (integerCyclotomicEvaluation A n T) := by
  apply CyclicRing.evaluate_ringStar_intertwining
    (Int.castRingHom (AdjoinRoot (cyclotomic n A)))
    (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
      (RamifiedConjugation.root_pow_order A n))
    (RamifiedConjugation.cyclotomicConjugation A n hn).toRingHom
  · intro r
    simp
  · exact cyclotomicPowerCharacter_neg A n hn

/-- A proved scalar norm equation in the integer group ring transfers to
the actual cyclotomic norm equation. -/
theorem integerCyclotomicEvaluation_norm (T : CyclicRing.Elem ℤ n) (a : ℤ)
    (hT : T * CyclicRing.ringStar T = CyclicRing.scalar n a) :
    integerCyclotomicEvaluation A n T *
      RamifiedConjugation.cyclotomicConjugation A n hn
        (integerCyclotomicEvaluation A n T) =
      (a : AdjoinRoot (cyclotomic n A)) := by
  rw [← integerCyclotomicEvaluation_ringStar A n hn, ← map_mul, hT,
    integerCyclotomicEvaluation_scalar]

end CirculantHadamard

end

end OAI
