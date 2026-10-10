import OAI.MeasureTheory.Falconer.Angular.CircleRotation
import OAI.MeasureTheory.Falconer.Graphs.GraphConeCutoff
import OAI.MeasureTheory.Falconer.Estimates.DistanceFormFubini

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable def sourceConeCircle (axis : ℝ) (dir : UnitCircle) : ℂ :=
  graphConeCutoff (sourceAngle (sourceCircleRotate (-axis) dir))

noncomputable def rotatedBinSelection (n : ℕ) (S : Finset ℕ) (axis : ℝ)
    (dir : UnitCircle) : ℂ :=
  ((∑ j ∈ S, circleAngularBin n j (sourceCircleRotate (-axis) dir) : ℝ) : ℂ)

theorem measurable_sourceConeCircle (axis : ℝ) : Measurable (sourceConeCircle axis) :=
  graphConeCutoff_contDiff.continuous.measurable.comp
    (measurable_sourceAngle.comp (sourceCircleRotate_isometry (-axis)).continuous.measurable)

theorem measurable_rotatedBinSelection (n : ℕ) (S : Finset ℕ) (axis : ℝ) :
    Measurable (rotatedBinSelection n S axis) := by
  apply Complex.measurable_ofReal.comp
  exact (Finset.measurable_sum S (fun j _ =>
    (circleAngularBin_continuous n j).measurable.comp
      (sourceCircleRotate_isometry (-axis)).continuous.measurable))

theorem sourceConeCircle_norm_le (axis : ℝ) (dir : UnitCircle) :
    ‖sourceConeCircle axis dir‖ ≤ 1 := by
  simp only [sourceConeCircle, graphConeCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg graphConeBump.nonneg]
  exact graphConeBump.le_one

theorem rotatedBinSelection_norm_le (n : ℕ) (S : Finset ℕ) (axis : ℝ) (dir : UnitCircle) :
    ‖rotatedBinSelection n S axis dir‖ ≤ 1 := by
  have hb := selectedAngularBins_bounds n S (sourceAngle (sourceCircleRotate (-axis) dir))
  simpa only [rotatedBinSelection, circleAngularBin, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb.1] using hb.2

theorem sourceAngle_comp_on_period {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    sourceAngle (sourceUnitDirection θ) = θ := by
  rw [sourceAngle_sourceUnitDirection]
  exact_mod_cast Complex.arg_cos_add_sin_mul_I hθ

theorem sourceConeCircle_rotate (axis θ : ℝ) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    sourceConeCircle axis (sourceCircleRotate axis (sourceUnitDirection θ)) = graphConeCutoff θ := by
  simp only [sourceConeCircle, sourceCircleRotate_add, add_neg_cancel, sourceCircleRotate_zero,
    sourceAngle_comp_on_period hθ]

theorem rotatedBinSelection_rotate (n : ℕ) (S : Finset ℕ) (axis θ : ℝ) :
    rotatedBinSelection n S axis (sourceCircleRotate axis (sourceUnitDirection θ)) =
      ((∑ j ∈ S, periodicAngularBin n j θ : ℝ) : ℂ) := by
  simp only [rotatedBinSelection, sourceCircleRotate_add, add_neg_cancel,
    sourceCircleRotate_zero, circleAngularBin_comp]

theorem sourcePlaneWave_rotated (r axis φ θ : ℝ) {Δ : Plane}
    (hΔ : Δ = ‖Δ‖ • sourceDirection (φ+axis)) :
    sourcePlaneWave r (sourceCircleRotate axis (sourceUnitDirection θ)) Δ =
      cosineOscillator (r*‖Δ‖) (θ-φ) := by
  rw [sourceCircleRotate_comp]
  unfold sourcePlaneWave cosineOscillator
  change Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection (θ+axis)) Δ : ℂ)) = _
  conv_lhs => rw [hΔ, inner_smul_right, inner_sourceDirection]
  rw [show θ+axis-(φ+axis) = θ-φ by ring]
  push_cast
  congr 1
  ring

theorem sourceDistanceKernel_rotated_bins (axis r φ : ℝ) (δ : ℝ) (S : Finset ℕ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (x y : Plane)
    (hb₁ : Measurable (b₁ x)) (hb₂ : Measurable (b₂ y))
    (hΔ : x-y = ‖x-y‖ • sourceDirection (φ+axis)) :
    sourceDistanceKernel
      (fun dir => sourceConeCircle axis dir * rotatedBinSelection (angularBinCount δ) S axis dir)
      b₁ b₂ r x y =
    ∫ θ : ℝ, cosineOscillator (r*‖x-y‖) (θ-φ) *
      (graphConeCutoff θ * selectedBinAmplitude δ S
        (fun t => b₁ x (sourceUnitDirection (t+axis)) * conj (b₂ y (sourceUnitDirection (t+axis)))) θ) := by
  let F : UnitCircle → ℂ := fun dir => sourcePlaneWave r dir (x-y) *
    ((sourceConeCircle axis dir * rotatedBinSelection (angularBinCount δ) S axis dir) *
      b₁ x dir * conj (b₂ y dir))
  have hF : Measurable F := by
    apply Measurable.mul
    · unfold sourcePlaneWave
      fun_prop
    · exact (((measurable_sourceConeCircle axis).mul
        (measurable_rotatedBinSelection _ S axis)).mul hb₁).mul
        (Complex.continuous_conj.measurable.comp hb₂)
  change (∫ dir, F dir ∂sourceArcLength) = _
  rw [← sourceCircleRotate_integral axis hF]
  have hrot : AEStronglyMeasurable (fun dir => F (sourceCircleRotate axis dir)) sourceArcLength :=
    (hF.comp (sourceCircleRotate_isometry axis).continuous.measurable).aestronglyMeasurable
  rw [sourceArcLength_integral_period hrot]
  let G : ℝ → ℂ := fun θ => cosineOscillator (r*‖x-y‖) (θ-φ) *
    (graphConeCutoff θ * selectedBinAmplitude δ S
      (fun t => b₁ x (sourceUnitDirection (t+axis)) * conj (b₂ y (sourceUnitDirection (t+axis)))) θ)
  have hs : Function.support G ⊆ Ioc (-Real.pi) Real.pi := by
    intro θ hθ
    have hw : graphConeCutoff θ ≠ 0 := by
      intro hz
      exact hθ (by simp [G, hz])
    have ht := graphConeCutoff_support (subset_closure hw)
    have hp := Real.one_le_pi_div_two
    exact ⟨by linarith only [ht.1, hp], by linarith only [ht.2, hp]⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with θ hθ
  have ht : θ ∈ Ioc (-Real.pi) Real.pi := by
    simpa only [uIoc_of_le (neg_le_self Real.pi_pos.le)] using hθ
  dsimp only [F, G]
  rw [sourcePlaneWave_rotated r axis φ θ hΔ, sourceConeCircle_rotate axis θ ht,
    rotatedBinSelection_rotate, sourceCircleRotate_comp]
  unfold selectedBinAmplitude
  ring

end PlanarFalconer

end OAI
