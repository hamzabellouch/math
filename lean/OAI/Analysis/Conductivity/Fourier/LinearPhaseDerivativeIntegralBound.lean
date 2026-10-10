import Mathlib
import OAI.Analysis.Conductivity.Flux.TwoFluxColumns

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem linear_phase_derivative_integral_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) (L : E →L[ℝ] ℝ) (hv : L v = 1)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val)
    (H : SmoothScalar ℝ) (C : ℝ) (hC : ∀ t, |H.val t| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    |∫ x, f.val x * (smoothDirection 1 H).val (k * L x) ∂μ| ≤
      k⁻¹ * C * ∫ x, |(smoothDirection v f).val x| ∂μ := by
  let g : SmoothScalar E := k⁻¹ • smoothPhase (k • L) H
  have hg : smoothDirection v g = smoothPhase (k • L) (smoothDirection 1 H) := by
    dsimp [g]
    rw [map_smul, smoothDirection_phase, smul_smul]
    simp [hv, hk.ne']
  have hibp := smooth_integration_by_parts μ v f g hf
  rw [hg] at hibp
  change (∫ x, f.val x * (smoothDirection 1 H).val (k * L x) ∂μ) = _ at hibp
  rw [hibp, abs_neg]
  have hi : Integrable (fun x => |(smoothDirection v f).val x|) μ :=
    ((smoothScalar_contDiff (smoothDirection v f)).continuous.abs).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection v hf).abs
  calc
    |∫ x, (smoothDirection v f).val x * g.val x ∂μ| ≤
        ∫ x, |(smoothDirection v f).val x * g.val x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (k⁻¹ * C) * |(smoothDirection v f).val x| ∂μ := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with x
        positivity
      · exact hi.const_mul _
      · filter_upwards [] with x
        change |(smoothDirection v f).val x * (k⁻¹ * H.val (k * L x))| ≤ _
        rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hk.le)]
        nlinarith [mul_le_mul_of_nonneg_left (hC (k * L x))
          (mul_nonneg (abs_nonneg ((smoothDirection v f).val x)) (inv_nonneg.mpr hk.le))]
    _ = _ := by rw [integral_const_mul]

theorem periodic_oscillations_weak
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val)
    (h : SmoothScalar ℝ) (hper : Function.Periodic h.val 1)
    (hmean : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    Filter.Tendsto (fun n : ℕ => ∫ x, f.val x * h.val ((n + 1 : ℝ) * L x) ∂μ)
      Filter.atTop (nhds 0) := by
  obtain ⟨v, hv⟩ : ∃ v, L v = 1 := by
    have hex : ∃ w, L w ≠ 0 := by
      by_contra hn
      apply hL
      ext w
      simpa using not_exists.mp hn w
    obtain ⟨w, hw⟩ := hex
    refine ⟨(L w)⁻¹ • w, ?_⟩
    simp [hw]
  obtain ⟨H₁, H₂, hd₁, hd₂, hp₁, hp₂, ⟨C, hb₁⟩, hb₂⟩ :=
    periodic_two_primitives h hper hmean
  have hb (n : ℕ) := linear_phase_derivative_integral_bound μ v L hv f hf H₁ C hb₁
    (by positivity : (0 : ℝ) < n + 1)
  simp only [hd₁] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n : ℕ => -((n + 1 : ℝ)⁻¹ * C * ∫ x, |(smoothDirection v f).val x| ∂μ))
    (h := fun n : ℕ => (n + 1 : ℝ)⁻¹ * C * ∫ x, |(smoothDirection v f).val x| ∂μ)
  · simpa using ((tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).mul_const C
      |>.mul_const (∫ x, |(smoothDirection v f).val x| ∂μ)).neg
  · simpa using ((tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).mul_const C
      |>.mul_const (∫ x, |(smoothDirection v f).val x| ∂μ))
  · exact fun n => (abs_le.mp (hb n)).1
  · exact fun n => (abs_le.mp (hb n)).2

end ScalarConductivity

end

end OAI
