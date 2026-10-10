import OAI.Analysis.CircleDomains.Sobolev.CurveCoareaInput
import OAI.Analysis.CircleDomains.Sobolev.LocalDerivativeCover
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! Differential-weighted curve coarea, derived from the published
constant-Lipschitz inequality by a disjoint local cover. No new coarea
input is assumed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem curve_coarea_lipschitzOn
    (hcoarea : PlanarLipschitzFiberCoarea) {A : Set ℂ} (hA : MeasurableSet A)
    (hfin : (μH[1] : Measure ℂ) A < ∞) {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f A) :
    AEMeasurable (fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) volume ∧
      (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
        (L : ℝ≥0∞) * (μH[1] : Measure ℂ) A := by
  obtain ⟨g, hg, he⟩ := hf.extend_real
  have hsets (t : ℝ) : A ∩ f ⁻¹' {t} = A ∩ g ⁻¹' {t} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact and_congr_right (fun hz => by rw [he hz])
  simpa only [hsets] using hcoarea A hA hfin L g hg

theorem smooth_curve_coarea_add_error
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
  obtain ⟨U, L, hU, hcover, _, hLip, hbound⟩ := exists_countable_derivative_cover hD hf hε
  let E : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hE (n : ℕ) : MeasurableSet (E n) :=
    hA.inter (MeasurableSet.disjointed (fun n => (hU n).measurableSet) n)
  have hEU (n : ℕ) : E n ⊆ U n := fun z hz => disjointed_subset U n hz.2
  have hEA (n : ℕ) : E n ⊆ A := inter_subset_left
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have hEq : (⋃ n, E n) = A := by
    ext z
    simp only [E, ← inter_iUnion, iUnion_disjointed, mem_inter_iff]
    exact ⟨And.left, fun hz => ⟨hz, hcover (hAD hz)⟩⟩
  have hpieces (n : ℕ) := curve_coarea_lipschitzOn hcoarea (hE n)
    ((measure_mono (hEA n)).trans_lt hfin) ((hLip n).mono (hEU n))
  have hcount (t : ℝ) : (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t}) ≤
      ∑' n, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t}) := by
    rw [← hEq, iUnion_inter]
    exact measure_iUnion_le _
  calc
    (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
        ∫⁻ t, ∑' n, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t}) := lintegral_mono hcount
    _ = ∑' n, ∫⁻ t, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t}) :=
      lintegral_tsum (fun n => (hpieces n).1)
    _ ≤ ∑' n, (L n : ℝ≥0∞) * (μH[1] : Measure ℂ) (E n) :=
      ENNReal.tsum_le_tsum (fun n => (hpieces n).2)
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

theorem smooth_curve_coarea_bound
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  have hbound (n : ℕ) := smooth_curve_coarea_add_error hcoarea hD hA hAD hfin hf
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
