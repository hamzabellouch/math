import Mathlib
import OAI.Analysis.WeakInfiniteness.SeparationFourColumns
import OAI.Analysis.WeakInfiniteness.SeparationScalar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def unitizedRight (a : A) (u : Unitization ℂ A) : A := ((a : Unitization ℂ A)*u).snd

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_unitizedRight (a : A) (u : Unitization ℂ A) :
    ((unitizedRight a u : A) : Unitization ℂ A)=(a : Unitization ℂ A)*u := inr_snd_inr_mul a u

lemma inr_factor_mem_principal {a x : A} (ha : 0 ≤ a) (u : Unitization ℂ A)
    (hx : (x : Unitization ℂ A)=(a : Unitization ℂ A)*u) :
    x ∈ principalRightIdeal a := by
  have he : x=unitizedRight a u := by
    apply Unitization.inr_injective (R := ℂ)
    rw [inr_unitizedRight,hx]
  rw [he]
  exact unitizedRight_mem_principal a ha u

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_separationG (X : A) {l : ℝ} (hl : 0 < l) :
    ((cfcₙ (separationG l) (star X*X) : A) : Unitization ℂ A)=
      cfc (separationG l) (star (X : Unitization ℂ A)*(X : Unitization ℂ A)) := by
  rw [Unitization.real_cfcₙ_eq_cfc_inr _ _ (separationG_zero hl),Unitization.inr_mul,Unitization.inr_star]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_separationN (X : A) {l : ℝ} (hl : 0 < l) :
    ((cfcₙ (separationN l) (star X*X) : A) : Unitization ℂ A)=
      cfc (separationN l) (star (X : Unitization ℂ A)*(X : Unitization ℂ A)) := by
  rw [Unitization.real_cfcₙ_eq_cfc_inr _ _ (separationN_zero hl),Unitization.inr_mul,Unitization.inr_star]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_separationG (X : Unitization ℂ A) (l : ℝ) :
    ‖cfc (separationG l) (star X*X)‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro s _
  change ‖spectralRamp l (Real.sqrt s)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg _ _)]
  exact spectralRamp_le_one _ _

end

end

end WeakPureInfiniteness
end

end OAI
