import OAI.Analysis.CircleDomains.Sobolev.SmoothCurveCoarea

namespace OAI

/-! A smooth scalar image is paid by the integral of the differential
against curve length. This bound is proved directly by local Lipschitz
covers and therefore needs no additional published input. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem smooth_curve_image_add_error
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {ε : ℝ} (hε : 0 < ε) :
    volume (f '' A) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
  obtain ⟨U, L, hU, hcover, _, hLip, hbound⟩ := exists_countable_derivative_cover hD hf hε
  let E : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hE (n : ℕ) : MeasurableSet (E n) :=
    hA.inter (MeasurableSet.disjointed (fun n => (hU n).measurableSet) n)
  have hEU (n : ℕ) : E n ⊆ U n := fun z hz => disjointed_subset U n hz.2
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have hEq : (⋃ n, E n) = A := by
    ext z
    simp only [E, ← inter_iUnion, iUnion_disjointed, mem_inter_iff]
    exact ⟨And.left, fun hz => ⟨hz, hcover (hAD hz)⟩⟩
  calc
    volume (f '' A) = volume (⋃ n, f '' E n) := by rw [← image_iUnion, hEq]
    _ ≤ ∑' n, volume (f '' E n) := measure_iUnion_le _
    _ ≤ ∑' n, (L n : ℝ≥0∞) * (μH[1] : Measure ℂ) (E n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have h := ((hLip n).mono (hEU n)).hausdorffMeasure_image_le (d := 1) (by norm_num)
      simpa only [hausdorffMeasure_real, ENNReal.rpow_one] using h
    _ ≤ ∑' n, ∫⁻ z in E n, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← setLIntegral_const]
      apply setLIntegral_mono' (hE n)
      intro z hz
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (norm_nonneg _) hε.le]
      exact ENNReal.ofReal_le_ofReal (hbound n z (hEU n hz))
    _ = ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
      rw [← lintegral_iUnion hE hdisj, hEq]

theorem smooth_curve_image_bound
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    volume (f '' A) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  have hbound (n : ℕ) := smooth_curve_image_add_error hD hA hAD hf
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  simp only [lintegral_add_right _ measurable_const, setLIntegral_const] at hbound
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hp := ENNReal.Tendsto.mul_const ht (Or.inr hfin.ne)
  have hall := (tendsto_const_nhds (x :=
    ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ))).add hp
  simp only [zero_mul, add_zero] at hall
  exact ge_of_tendsto hall (Eventually.of_forall hbound)

end CircleDomainRigidity

end

end OAI
