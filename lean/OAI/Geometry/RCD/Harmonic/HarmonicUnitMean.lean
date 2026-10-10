import OAI.Geometry.RCD.Harmonic.HarmonicSmallNorm

namespace OAI

/-! # The harmonic L² mean-value bound at unit rescaled curvature -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Rescaling the actual harmonic function removes the smallness condition
in the level-set argument. -/
theorem NoncollapsedRCD.harmonic_unit_mean_value {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ u : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball x R) u →
      ∀ᵐ y ∂(hausdorff n X).restrict (ball x (R/2)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic u y| ≤
          C*harmonicTargetNorm hX x R u := by
  obtain ⟨δ,hδ,hsmall⟩ := hX.harmonic_small_l2_upper_bound hn
  let C := 1+(Real.sqrt δ)⁻¹
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hC : 1 ≤ C := le_add_of_nonneg_right (inv_nonneg.mpr hsd.le)
  refine ⟨C,hC,?_⟩
  intro x R hR hcurv u hu
  let μ := hausdorff n X
  let U := SobolevSpace.toLp μ hX.quadratic u
  let V := μ.real (ball x R)
  let T := harmonicTargetNorm hX x R u
  let I := ∫ y in ball x R, (U y)^2 ∂μ
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hT : 0 ≤ T := norm_nonneg _
  have hnorm : T^2 = V⁻¹*I := normalized_sobolev_mean_sq μ hX.quadratic
    (ball x R) (hX.finiteOnBounded _ isBounded_ball).ne u
  have hI : I = T^2*V := by
    rw [hnorm]
    field_simp
  by_cases hTz : T = 0
  · have hIz : I = 0 := by rw [hI,hTz,zero_pow (by decide),zero_mul]
    have hz := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (U y))
      (Lp.memLp U).integrable_sq.integrableOn).mp hIz
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : R/2 ≤ R)) hz] with y hy
    have hy0 : U y = 0 := sq_eq_zero_iff.mp hy
    change |U y| ≤ C*T
    rw [hy0,hTz,abs_zero,mul_zero]
  have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hTz)
  let c := Real.sqrt δ/T
  have hc : 0 < c := div_pos hsd hTp
  have hc2 : c^2 = δ/T^2 := by
    dsimp only [c]
    rw [div_pow,Real.sq_sqrt hδ.le]
  have hscale (a : ℝ) : (∫ y in ball x R,
      (SobolevSpace.toLp μ hX.quadratic (a • u) y)^2 ∂μ) = a^2*I := by
    have he : SobolevSpace.toLp μ hX.quadratic (a • u) =ᵐ[μ] fun y => a*U y := by
      rw [map_smul]
      exact Lp.coeFn_smul _ _
    rw [integral_congr_ae ((ae_restrict_of_ae he).mono fun y hy => congrArg (fun t : ℝ => t^2) hy)]
    simp_rw [mul_pow]
    exact integral_const_mul _ _
  have hsplus : (∫ y in ball x R,
      (SobolevSpace.toLp μ hX.quadratic (c • u) y)^2 ∂μ) ≤ δ*V := by
    rw [hscale,hc2,hI]
    field_simp
    norm_num
  have hsminus : (∫ y in ball x R,
      (SobolevSpace.toLp μ hX.quadratic ((-c) • u) y)^2 ∂μ) ≤ δ*V := by
    rw [hscale,neg_sq,hc2,hI]
    field_simp
    norm_num
  have hp := hsmall x R hR hcurv (c • u) (hu.smul μ hX.quadratic c) hsplus
  have hm := hsmall x R hR hcurv ((-c) • u) (hu.smul μ hX.quadratic (-c)) hsminus
  have hpcoe : SobolevSpace.toLp μ hX.quadratic (c • u) =ᵐ[μ] fun y => c*U y := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hmcoe : SobolevSpace.toLp μ hX.quadratic ((-c) • u) =ᵐ[μ] fun y => (-c)*U y := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hlarge : 1 ≤ c*(C*T) := by
    have he : c*(C*T) = Real.sqrt δ+1 := by
      dsimp only [c,C]
      field_simp
    rw [he]
    linarith
  filter_upwards [hp,hm,ae_restrict_of_ae hpcoe,ae_restrict_of_ae hmcoe] with y hyp hym hep hem
  rw [hep] at hyp
  rw [hem] at hym
  have habs : c*|U y| ≤ 1 := by
    rw [← abs_of_pos hc,← abs_mul]
    exact abs_le.mpr ⟨by nlinarith, hyp⟩
  exact (mul_le_mul_iff_right₀ hc).mp (habs.trans hlarge)

end RegularPointCoordinates

end

end OAI
