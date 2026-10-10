import OAI.Geometry.Perimeter.Regularity.FlatExcess

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem normal_flux_error_le_tilt (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {R : ℝ} (hR : 0 < R)
    {ψ : Euc n → ℝ} (hψ : Measurable ψ) {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) :
    |(∫ x in Metric.ball 0 R, ψ x ∂perimeterMeasure E) -
      (∫ x in Metric.ball 0 R, ψ x*inner ℝ (approximateNormal E x) v ∂perimeterMeasure E)| ≤
      M * orientedTilt E v (Metric.ball 0 R) / 2 := by
  let μ := (perimeterMeasure E).restrict (Metric.ball 0 R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ,perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 0 R hR⟩
  have hM0 : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
  have hiψ : Integrable ψ μ := Integrable.of_bound hψ.aestronglyMeasurable M (ae_of_all _ hM)
  have hN : ∀ x, |inner ℝ (approximateNormal E x) v| ≤ 1 := by
    intro x
    exact (abs_real_inner_le_norm _ _).trans (by rw [hv,mul_one]; exact approximateNormal_norm_le_one E x)
  have hif : Integrable (fun x ↦ ψ x*inner ℝ (approximateNormal E x) v) μ := by
    apply Integrable.of_bound (hψ.mul
      ((measurable_approximateNormal hmin.1).inner measurable_const)).aestronglyMeasurable M
    apply ae_of_all _
    intro x
    change ‖ψ x*inner ℝ (approximateNormal E x) v‖ ≤ M
    rw [norm_mul]
    exact (mul_le_mul (hM x) (hN x) (abs_nonneg _) hM0).trans_eq (mul_one _)
  have htilt : Integrable (fun x ↦ ‖approximateNormal E x-v‖^2) μ := by
    apply Integrable.of_bound
      (((measurable_approximateNormal hmin.1).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      4
    apply ae_of_all _
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have h := (norm_sub_le (approximateNormal E x) v).trans
      (show ‖approximateNormal E x‖+‖v‖ ≤ 2 by rw [hv]; linarith [approximateNormal_norm_le_one E x])
    change ‖approximateNormal E x-v‖^2 ≤ 4
    nlinarith [norm_nonneg (approximateNormal E x-v)]
  have hdiff : ∀ᵐ x ∂μ, |ψ x-ψ x*inner ℝ (approximateNormal E x) v| ≤
      (M/2)*‖approximateNormal E x-v‖^2 := by
    filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)] with x hx
    have hid : 1-inner ℝ (approximateNormal E x) v = ‖approximateNormal E x-v‖^2/2 := by
      rw [norm_sub_sq_real,hx.1,hv]
      ring
    rw [show ψ x-ψ x*inner ℝ (approximateNormal E x) v =
      ψ x*(1-inner ℝ (approximateNormal E x) v) by ring,
      abs_mul,hid,abs_of_nonneg (show 0 ≤ ‖approximateNormal E x-v‖^2/2 by positivity)]
    have h := mul_le_mul_of_nonneg_right (hM x) (by positivity : 0 ≤ ‖approximateNormal E x-v‖^2/2)
    simpa only [Real.norm_eq_abs,mul_div_assoc,div_mul_eq_mul_div] using h
  change |(∫ x, ψ x ∂μ)-(∫ x, ψ x*inner ℝ (approximateNormal E x) v ∂μ)| ≤ _
  rw [← integral_sub hiψ hif]
  calc
    _ ≤ ∫ x, |ψ x-ψ x*inner ℝ (approximateNormal E x) v| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (M/2)*‖approximateNormal E x-v‖^2 ∂μ :=
      integral_mono_ae (hiψ.sub hif).abs (htilt.const_mul _) hdiff
    _ = _ := by rw [integral_const_mul]; dsimp only [orientedTilt,μ]; ring

end RPISingularHarnack

end

end OAI
