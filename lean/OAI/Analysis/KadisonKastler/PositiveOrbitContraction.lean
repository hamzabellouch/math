import OAI.Analysis.KadisonKastler.ProjectionReflectionOrbit
import OAI.Analysis.KadisonKastler.UniformProjectionGap
import OAI.Analysis.KadisonKastler.PositiveConeFaithfulApproximation
import OAI.Analysis.KadisonKastler.PositiveReferenceModular

namespace OAI

/-! # A uniform contraction in the orbit of positive unit vectors -/

namespace KadisonKastler
open Generator.Tracial NormedSpace
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveOrbitContractionReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

omit [TopologicalSpace.SeparableSpace H] in
private theorem normalized_defect_norm (J : H ≃ₗᵢ⋆[ℂ] H) (p : AlgebraProjection M)
    (x : H) :
    ‖centralVectorDefect J x p.val.val‖ =
      ‖x‖*‖centralVectorDefect J (normalize x) p.val.val‖ := by
  have he : centralVectorDefect J x p.val.val =
      ‖x‖ • centralVectorDefect J (normalize x) p.val.val := by
    conv_lhs => rw [← norm_smul_normalize x]
    simp only [centralVectorDefect_apply,ContinuousLinearMap.map_smul_of_tower,smul_sub]
  rw [he,norm_smul,Real.norm_of_nonneg (norm_nonneg x)]

theorem positive_orbit_distance_contraction
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (Ω : H) (hΩ : J Ω=Ω)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ Ω (modularQuadratic J a Ω))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (x y : H) (hx : x ∈ modularPositiveCone (M := M) J Ω)
    (hy : y ∈ modularPositiveCone (M := M) J Ω)
    (hxn : ‖x‖=1) (hyn : ‖y‖=1)
    (hxs : Function.Injective (algebraVectorMap M x)) :
    ∃ u : unitary (Algebra M),
      ‖x-(modularUnitary J hJ u : H →L[ℂ] H) y‖^2 ≤
        (1-1/16777216:ℝ)*‖x-y‖^2 := by
  by_cases hxy : x=y
  · refine ⟨1,?_⟩
    subst y
    simp [modularUnitary,conjugationUnitary,ambientAlgebraUnitary,conjugationOperator,hJ x]
  have hxJ := modularPositiveCone_fixed J hright Ω hΩ hx
  have hyJ := modularPositiveCone_fixed J hright Ω hΩ hy
  have hsd : inner ℂ (x+y) (x-y)=0 := by
    have he : inner ℂ y x=inner ℂ x y := by
      rw [← inner_conj_symm y x,symmetric_inner_real J x y hxJ hyJ]
      simp
    rw [inner_add_left,inner_sub_right,inner_sub_right,
      inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,hxn,hyn,he]
    ring
  have hs : x+y≠0 := by
    have he := norm_add_sq_real x y
    rw [hxn,hyn] at he
    have hnonneg := modularPositiveCone_acute J hJ hright Ω hpos hx hy
    intro hz
    rw [hz,norm_zero] at he
    linarith
  have hd : x-y≠0 := sub_ne_zero.mpr hxy
  have hsum := (modularPositiveCone J Ω).add_mem hx hy
  have hr : normalize (x+y) ∈ modularPositiveCone (M := M) J Ω :=
    (modularPositiveCone J Ω).smul_mem (inv_pos.mpr (norm_pos_iff.mpr hs)) hsum
  have hrs : Function.Injective (algebraVectorMap M (normalize (x+y))) := by
    have hsep := positiveCone_separating_add J hJ hright Ω hΩ hpos hx hy hxs
    intro a b hab
    apply hsep
    change a.val (‖x+y‖⁻¹ • (x+y))=b.val (‖x+y‖⁻¹ • (x+y)) at hab
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
    exact smul_right_injective H (inv_ne_zero (norm_ne_zero_iff.mpr hs)) hab
  have hzJ : J (normalize (x-y))=normalize (x-y) := by
    change J (‖x-y‖⁻¹ • (x-y))=‖x-y‖⁻¹ • (x-y)
    rw [conjugateIsometry_real_smul,map_sub,hxJ,hyJ]
  have horth : inner ℂ (normalize (x+y)) (normalize (x-y))=0 := by
    change inner ℂ ((‖x+y‖⁻¹ : ℝ) • (x+y)) ((‖x-y‖⁻¹ : ℝ) • (x-y))=0
    simp only [inner_smul_left_eq_smul,inner_smul_right_eq_smul,hsd,smul_zero]
  obtain ⟨p,hp,hq⟩ := exists_uniform_projection_gap J hJ hright hleft (normalize (x+y))
    (modularPositiveCone_fixed J hright Ω hΩ hr) (norm_normalize hs) hrs
    (fun a => positiveCone_quadratic_nonneg J hJ hright Ω hpos hr a) hIII hremote
    (normalize (x-y)) hzJ (norm_normalize hd) horth
    (‖x-y‖^2/67108864) (by positivity)
  refine ⟨projectionOrbitReflection p,?_⟩
  rw [projectionOrbitReflection_distance J hJ hright]
  have hsumBound : ‖x+y‖^2 ≤ 4 := by
    have hn := norm_add_le x y
    rw [hxn,hyn] at hn
    nlinarith [norm_nonneg (x+y)]
  have hsumDef : ‖centralVectorDefect J (x+y) p.val.val‖^2 <
      ‖x-y‖^2/16777216 := by
    rw [normalized_defect_norm J p (x+y),mul_pow]
    calc
      _ ≤ 4*‖centralVectorDefect J (normalize (x+y)) p.val.val‖^2 :=
        mul_le_mul_of_nonneg_right hsumBound (sq_nonneg _)
      _ < _ := by linarith
  have hdiffDef : ‖x-y‖^2/8388608 < ‖centralVectorDefect J (x-y) p.val.val‖^2 := by
    rw [normalized_defect_norm J p (x-y),mul_pow]
    have hm := mul_lt_mul_of_pos_left hq (sq_pos_of_pos (norm_pos_iff.mpr hd))
    nlinarith only [hm]
  linarith

end
end KadisonKastler

end OAI
