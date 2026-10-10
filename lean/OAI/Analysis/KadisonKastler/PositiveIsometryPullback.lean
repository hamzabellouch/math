import OAI.Analysis.KadisonKastler.ModularIsometryCorner
import OAI.Analysis.KadisonKastler.PositiveReferenceHaagerup
import OAI.Analysis.KadisonKastler.PositiveConeFaithfulApproximation
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # Faithful positive references pulled back from a modular corner -/

namespace KadisonKastler

open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positivePullbackRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ=ξ)
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ hright hξ hpos in
theorem positive_isometry_pullback_separating {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η))
    (v : Algebra M) (hv : star v*v=1) :
    Function.Injective (algebraVectorMap M (modularQuadratic J (star v) η)) := by
  intro a b hab
  have hz : (a-b).val (modularQuadratic J (star v) η)=0 := sub_eq_zero.mpr hab
  have hq : modularQuadratic J ((a-b)*star v) η=0 := by
    rw [← modularQuadratic_mul J hJ hright]
    change (a-b).val (conjugationOperator J (a-b).val (modularQuadratic J (star v) η))=0
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (a-b)) (a-b).val (a-b).property
    rw [← mul_apply_eq_comp,hc,mul_apply_eq_comp,hz,map_zero]
  have hk := positiveCone_operator_kills_of_quadratic_kills J hJ hright ξ hξ hpos hη
    ((a-b)*star v) hq
  have he : (a-b)*star v=0 := hsep (hk.trans (map_zero (algebraVectorMap M η)).symm)
  have ht := congrArg (fun c : Algebra M => c*v) he
  rw [mul_assoc,hv,mul_one,zero_mul] at ht
  exact sub_eq_zero.mp ht

include hJ hright hξ hpos in
theorem positive_isometry_pullback_nonzero {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η)) (hne : η≠0)
    (v : Algebra M) (hv : star v*v=1) : modularQuadratic J (star v) η≠0 := by
  intro hz
  have hs := positive_isometry_pullback_separating J hJ hright ξ hξ hpos hη hsep v hv
  have he : (1 : Algebra M)=0 := hs (by
    change (1 : H →L[ℂ] H) (modularQuadratic J (star v) η)=
      (0 : H →L[ℂ] H) (modularQuadratic J (star v) η)
    simp only [one_apply_eq_self,zero_apply,hz])
  have heη := congrArg (fun a : Algebra M => a.val η) he
  exact hne (by simpa only [OneMemClass.coe_one,one_apply_eq_self,
    ZeroMemClass.coe_zero,zero_apply] using heη)

include hJ hright hξ hpos in
theorem positive_isometry_pullback_normalized {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η)) (hne : η≠0)
    (v : Algebra M) (hv : star v*v=1) :
    normalize (modularQuadratic J (star v) η) ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M (normalize (modularQuadratic J (star v) η))) ∧
      ‖normalize (modularQuadratic J (star v) η)‖=1 := by
  let z := modularQuadratic J (star v) η
  have hz : z≠0 := positive_isometry_pullback_nonzero J hJ hright ξ hξ hpos hη hsep hne v hv
  have hs := positive_isometry_pullback_separating J hJ hright ξ hξ hpos hη hsep v hv
  refine ⟨?_,?_,norm_normalize hz⟩
  · exact (modularPositiveCone J ξ).smul_mem (inv_pos.mpr (norm_pos_iff.mpr hz))
      (modularQuadratic_preserves_positiveCone J hJ hright ξ (star v) hη)
  · intro a b hab
    apply hs
    change a.val (‖z‖⁻¹ • z)=b.val (‖z‖⁻¹ • z) at hab
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
    exact smul_right_injective H (inv_ne_zero (norm_ne_zero_iff.mpr hz)) hab

end

end KadisonKastler

end OAI
