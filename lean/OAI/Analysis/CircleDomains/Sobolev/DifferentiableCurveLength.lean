import OAI.Analysis.CircleDomains.Topology.ApproximateCurveDistances
import OAI.Analysis.CircleDomains.Topology.CurveHausdorffLower

namespace OAI

/-! Exact arclength on a bounded Borel set where a plane curve is differentiable.
No continuity of the derivative or open-domain assumption is used. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_curve_upper_error {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x)
    {ε : ℝ} (hε : 0 < ε) :
    (μH[1] : Measure ℂ) (γ '' S) ≤
      (∫⁻ t in S, ENNReal.ofReal ‖d t‖) + ENNReal.ofReal ε * volume S := by
  obtain ⟨B, K, k, hB, hdj, hcov, hLip, _, hnorm⟩ :=
    differentiable_curve_distance_partition hS hd hε
  calc
    (μH[1] : Measure ℂ) (γ '' S) = (μH[1] : Measure ℂ) (⋃ n, γ '' B n) := by
      rw [← image_iUnion, hcov]
    _ ≤ ∑' n, (μH[1] : Measure ℂ) (γ '' B n) := measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ t in B n, ENNReal.ofReal (‖d t‖+ε) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hb : (μH[1] : Measure ℂ) (γ '' B n) ≤ (K n : ℝ≥0∞)*volume (B n) := by
        simpa only [ENNReal.rpow_one, hausdorffMeasure_real] using
          (hLip n).hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1)
      apply hb.trans
      rw [← Measure.restrict_apply_univ, ← lintegral_const]
      apply lintegral_mono_ae
      filter_upwards [hnorm n] with t ht
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal ht.1
    _ = ∫⁻ t in S, ENNReal.ofReal (‖d t‖+ε) := by
      rw [← lintegral_iUnion hB hdj, hcov]
    _ = (∫⁻ t in S, ENNReal.ofReal ‖d t‖)+ENNReal.ofReal ε*volume S := by
      simp_rw [ENNReal.ofReal_add (norm_nonneg _) hε.le]
      rw [lintegral_add_right (f := fun t => ENNReal.ofReal ‖d t‖)
        (g := fun _ => ENNReal.ofReal ε) measurable_const]
      simp only [lintegral_const, Measure.restrict_apply_univ]

lemma differentiable_curve_lower_error {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x)
    (hi : InjOn γ S) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) ≤
      (μH[1] : Measure ℂ) (γ '' S) + ENNReal.ofReal ε * volume S := by
  obtain ⟨B, K, k, hB, hdj, hcov, _, hdist, hnorm⟩ :=
    differentiable_curve_distance_partition hS hd hε
  have hBS (n : ℕ) : B n ⊆ S := hcov ▸ subset_iUnion B n
  have hcont : ContinuousOn γ S := fun x hx => (hd x hx).continuousWithinAt
  have him (n : ℕ) : MeasurableSet (γ '' B n) :=
    (hB n).image_of_continuousOn_injOn (hcont.mono (hBS n)) (hi.mono (hBS n))
  have hidj : Pairwise (Disjoint on fun n => γ '' B n) := fun i j hij =>
    (hdj hij).image hi (hBS i) (hBS j)
  calc
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) = ∑' n, ∫⁻ t in B n, ENNReal.ofReal ‖d t‖ := by
      rw [← lintegral_iUnion hB hdj, hcov]
    _ ≤ ∑' n, ((μH[1] : Measure ℂ) (γ '' B n)+ENNReal.ofReal ε*volume (B n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hb : (∫⁻ t in B n, ENNReal.ofReal ‖d t‖) ≤
          ((k n : ℝ≥0∞)+ENNReal.ofReal ε)*volume (B n) := by
        rw [← Measure.restrict_apply_univ, ← lintegral_const]
        apply lintegral_mono_ae
        filter_upwards [hnorm n] with t ht
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg _) hε.le]
        exact ENNReal.ofReal_le_ofReal ht.2
      rw [add_mul] at hb
      exact hb.trans (add_le_add (lower_distance_hausdorff (Subset.rfl) (k n) (hdist n)) le_rfl)
    _ = (∑' n, (μH[1] : Measure ℂ) (γ '' B n))+ENNReal.ofReal ε*(∑' n, volume (B n)) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = (μH[1] : Measure ℂ) (γ '' S)+ENNReal.ofReal ε*volume S := by
      rw [← measure_iUnion hidj him, ← measure_iUnion hdj hB, ← image_iUnion, hcov]

lemma differentiable_curve_hausdorff_eq {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S)
    (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x) (hi : InjOn γ S) :
    (μH[1] : Measure ℂ) (γ '' S) = ∫⁻ t in S, ENNReal.ofReal ‖d t‖ := by
  have hεlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1:ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hvan : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1:ℝ))*volume S) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hεlim
      (Or.inr (hb.measure_lt_top (μ := volume)).ne)
  apply le_antisymm
  · have ht := (tendsto_const_nhds (x := ∫⁻ t in S, ENNReal.ofReal ‖d t‖)).add hvan
    simp only [add_zero] at ht
    exact ge_of_tendsto' ht (fun n => differentiable_curve_upper_error hS hd
      (ε := 1/(n+1:ℝ)) (one_div_pos.mpr (by positivity)))
  · have ht := (tendsto_const_nhds (x := (μH[1] : Measure ℂ) (γ '' S))).add hvan
    simp only [add_zero] at ht
    exact ge_of_tendsto' ht (fun n => differentiable_curve_lower_error hS hd hi
      (ε := 1/(n+1:ℝ)) (one_div_pos.mpr (by positivity)))

end CircleDomainRigidity

end

end OAI
