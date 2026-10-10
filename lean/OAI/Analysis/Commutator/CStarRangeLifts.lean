import Mathlib
import OAI.Analysis.Commutator.KaplanskyRational

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexStarModule CStarAlgebra

namespace Kadison.CStarRangeLifts

open Kaplansky ComplexStarModule

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable (φ : A →⋆ₐ[ℂ] B)

theorem selfAdjoint_contraction {b : B} (hb : IsSelfAdjoint b) (hn : ‖b‖≤1)
    (hr : b∈Set.range φ) : ∃ a : A, IsSelfAdjoint a ∧ ‖a‖≤1 ∧ φ a=b := by
  obtain ⟨a,ha⟩ := hr
  let a₀ : A := ℜ a
  have ha₀ : IsSelfAdjoint a₀ := (ℜ a).property
  have he : φ a₀=b := by rw [show a₀=(ℜ a:A) from rfl,map_realPart,ha,hb.coe_realPart]
  refine ⟨clip (lift a₀),clip_selfAdjoint _,clip_norm_le _,?_⟩
  rw [clip,φ.map_cfc rationalClip (lift a₀) continuous_rationalClip.continuousOn
    (by fun_prop) (lift_selfAdjoint _) ((lift_selfAdjoint a₀).map φ),lift,
    φ.map_cfc rationalLift a₀ continuous_rationalLift.continuousOn (by fun_prop) ha₀ (ha₀.map φ),he]
  exact clip_lift hb hn

theorem contraction {b : B} (hn : ‖b‖≤1) (hr : b∈Set.range φ) :
    ∃ a : A, ‖a‖≤2 ∧ φ a=b := by
  obtain ⟨a,ha⟩ := hr
  obtain ⟨x,hx,hnx,hex⟩ := selfAdjoint_contraction φ (ℜ b).property
    ((realPart.norm_le b).trans hn) ⟨(ℜ a:A),by rw [map_realPart,ha]⟩
  obtain ⟨y,hy,hny,hey⟩ := selfAdjoint_contraction φ (ℑ b).property
    ((imaginaryPart.norm_le b).trans hn) ⟨(ℑ a:A),by rw [map_imaginaryPart,ha]⟩
  refine ⟨x+Complex.I • y,?_,?_⟩
  · calc
      _≤‖x‖+‖Complex.I • y‖ := norm_add_le _ _
      _=‖x‖+‖y‖ := by rw [norm_smul,Complex.norm_I,one_mul]
      _≤2 := by linarith
  · rw [map_add,map_smul,hex,hey,realPart_add_I_smul_imaginaryPart]

end Kadison.CStarRangeLifts

end

end
end

end OAI
