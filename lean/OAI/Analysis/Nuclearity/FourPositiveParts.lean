import Mathlib

namespace OAI

/-! Four positive parts suffice to test complex-linear identities at one
C*-algebra element. -/

noncomputable section
open Complex selfAdjoint

namespace WeakPureInfiniteness

variable {D E : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [AddCommGroup E] [Module ℂ E]

def fourPositiveParts (x : D) : Fin 4 → D :=
  ![(realPart x : D)⁺, (realPart x : D)⁻,
    (imaginaryPart x : D)⁺, (imaginaryPart x : D)⁻]

lemma fourPositiveParts_nonneg (x : D) (j : Fin 4) : 0 ≤ fourPositiveParts x j := by
  fin_cases j
  · exact CFC.posPart_nonneg _
  · exact CFC.negPart_nonneg _
  · exact CFC.posPart_nonneg _
  · exact CFC.negPart_nonneg _

omit [PartialOrder D] [StarOrderedRing D] in
lemma fourPositiveParts_decomposition (x : D) :
    x = (fourPositiveParts x 0 - fourPositiveParts x 1) +
      Complex.I • (fourPositiveParts x 2 - fourPositiveParts x 3) := by
  change x = ((realPart x : D)⁺ - (realPart x : D)⁻) +
    Complex.I • ((imaginaryPart x : D)⁺ - (imaginaryPart x : D)⁻)
  rw [CFC.posPart_sub_negPart _ (realPart x).property,
    CFC.posPart_sub_negPart _ (imaginaryPart x).property]
  exact (realPart_add_I_smul_imaginaryPart x).symm

omit [PartialOrder D] [StarOrderedRing D] in
lemma linearMap_eq_of_fourPositiveParts (f g : D →ₗ[ℂ] E) (x : D)
    (h : ∀ j, f (fourPositiveParts x j) = g (fourPositiveParts x j)) : f x = g x := by
  rw [fourPositiveParts_decomposition x]
  simp only [map_add, map_sub, map_smul, h]

end WeakPureInfiniteness

end

end OAI
