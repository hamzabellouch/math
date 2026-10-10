import OAI.Analysis.KadisonKastler.PositiveVectorPinching
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # A nearby faithful positive unit vector centralizing a projection

Two-sided pinching followed by normalization costs at most twice the
original left-right projection gap.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance normalizedPinchRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

omit [CompleteSpace H] in
theorem norm_normalize_sub_le_twice {x y : H} (hx : ‖x‖ = 1) (hy : y ≠ 0) :
    ‖normalize y - x‖ ≤ 2 * ‖y-x‖ := by
  have hn : ‖normalize y‖ = 1 := norm_normalize hy
  have he : normalize y - y = (1-‖y‖) • normalize y := by
    rw [sub_smul,one_smul,norm_smul_normalize]
  have hb : ‖normalize y-y‖ ≤ ‖y-x‖ := by
    rw [he,norm_smul,hn,mul_one,Real.norm_eq_abs,abs_sub_comm]
    simpa only [hx] using abs_norm_sub_norm_le y x
  calc
    ‖normalize y - x‖ = ‖(normalize y - y) + (y - x)‖ := by congr 1; abel
    _ ≤ ‖normalize y-y‖ + ‖y-x‖ := norm_add_le _ _
    _ ≤ 2 * ‖y-x‖ := by linarith

theorem exists_positive_projection_central_unit_vector
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) (hunit : ‖ξ‖ = 1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (p : AlgebraProjection M)
    (hgap : ‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ < 1) :
    ∃ ζ : H, ‖ζ‖ = 1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      p.val.val ζ = conjugationOperator J p.val.val ζ ∧
      ‖ζ-ξ‖ ≤ 2 * ‖p.val.val ξ-conjugationOperator J p.val.val ξ‖ := by
  let y := positiveVectorPinch J p ξ
  have he := positiveVectorPinch_norm_sub J hJ hright p ξ
  have hy : y ≠ 0 := by
    intro hz
    change ‖y-ξ‖ = _ at he
    rw [hz,zero_sub,norm_neg,hunit] at he
    linarith
  have hycone := positiveVectorPinch_mem_cone J hJ hright ξ p
    (reference_mem_modularPositiveCone J hJ ξ)
  have hysep := positiveVectorPinch_separating J hJ hright ξ hξ hpos p
    (reference_mem_modularPositiveCone J hJ ξ) hsep
  have hscalar : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy)
  have hζcone : normalize y ∈ modularPositiveCone (M := M) J ξ :=
    (modularPositiveCone J ξ).smul_mem hscalar hycone
  have hζsep : Function.Injective (algebraVectorMap M (normalize y)) := by
    intro a b hab
    apply hysep
    change a.val y = b.val y
    change a.val (‖y‖⁻¹ • y) = b.val (‖y‖⁻¹ • y) at hab
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
    exact smul_right_injective H hscalar.ne' hab
  refine ⟨normalize y,norm_normalize hy,hζcone,hζsep,?_,?_⟩
  · change p.val.val (‖y‖⁻¹ • y) = conjugationOperator J p.val.val (‖y‖⁻¹ • y)
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower]
    exact congrArg (fun z : H => ‖y‖⁻¹ • z)
      (positiveVectorPinch_centralizes_projection J hJ hright p ξ)
  · exact (norm_normalize_sub_le_twice hunit hy).trans_eq (congrArg (2 * ·) he)

end

end KadisonKastler

end OAI
