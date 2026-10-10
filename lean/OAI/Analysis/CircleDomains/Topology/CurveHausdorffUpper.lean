import OAI.Analysis.CircleDomains.Sobolev.DerivativeLipschitzPartition
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The upper arclength bound for a C1 plane curve, first with an arbitrary
positive error, then exactly on every bounded Borel subset of its domain. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma curve_hausdorff_upper_add_error
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {S : Set ℝ} (hS : MeasurableSet S) (hSD : S ⊆ D) {ε : ℝ} (hε : 0 < ε) :
    (μH[1] : Measure ℂ) (γ '' S) ≤
      (∫⁻ t in S, ENNReal.ofReal ‖d t‖) + ENNReal.ofReal ε * volume S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨A, K, hA, hdisj, hcover, hLip, hnorm⟩ :=
    derivative_lipschitz_partition hD (hne.mono hSD) hd hc hε
  have hsets : (⋃ n, S ∩ A n) = S := by
    rw [← inter_iUnion, hcover, inter_eq_left.mpr hSD]
  calc
    (μH[1] : Measure ℂ) (γ '' S) =
        (μH[1] : Measure ℂ) (⋃ n, γ '' (S ∩ A n)) := by rw [← image_iUnion, hsets]
    _ ≤ ∑' n, (μH[1] : Measure ℂ) (γ '' (S ∩ A n)) := measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ t in S ∩ A n, ENNReal.ofReal (‖d t‖ + ε) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hbound : (μH[1] : Measure ℂ) (γ '' (S ∩ A n)) ≤
          (K n : ℝ≥0∞) * volume (S ∩ A n) := by
        simpa only [ENNReal.rpow_one, hausdorffMeasure_real] using
          ((hLip n).mono inter_subset_right).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
      apply hbound.trans
      rw [← Measure.restrict_apply_univ, ← lintegral_const]
      apply setLIntegral_mono' (hS.inter (hA n))
      intro t ht
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hnorm n t ht.2)
    _ = ∫⁻ t in S, ENNReal.ofReal (‖d t‖ + ε) := by
      rw [← lintegral_iUnion (fun n => hS.inter (hA n))
        (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right), hsets]
    _ = (∫⁻ t in S, ENNReal.ofReal ‖d t‖) + ENNReal.ofReal ε * volume S := by
      simp_rw [ENNReal.ofReal_add (norm_nonneg _) hε.le]
      rw [lintegral_add_right (f := fun t => ENNReal.ofReal ‖d t‖)
        (g := fun _ => ENNReal.ofReal ε) measurable_const]
      simp only [lintegral_const, Measure.restrict_apply_univ]

lemma curve_hausdorff_upper
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    (μH[1] : Measure ℂ) (γ '' S) ≤ ∫⁻ t in S, ENNReal.ofReal ‖d t‖ := by
  have hεlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := (tendsto_const_nhds (x := ∫⁻ t in S, ENNReal.ofReal ‖d t‖)).add
    (ENNReal.Tendsto.mul_const hεlim (Or.inr (hb.measure_lt_top (μ := volume)).ne))
  simp only [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht (fun (n : ℕ) => curve_hausdorff_upper_add_error hD hd hc hS hSD (ε := 1 / (n + 1 : ℝ)) (by exact one_div_pos.mpr (by positivity)))

end CircleDomainRigidity

end

end OAI
