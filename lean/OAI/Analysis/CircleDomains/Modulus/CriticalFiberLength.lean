import OAI.Analysis.CircleDomains.Sobolev.LipschitzLengthFiberMajorant
import OAI.Analysis.CircleDomains.Sobolev.LocalDerivativeCover
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! Critical points of a C1 scalar planar map contribute zero fiber length
for almost every level. No assertion that C1 critical values have measure
zero is used. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma critical_fiber_majorant
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {A : Set ℂ} (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) A := by
  obtain ⟨U, L, hU, hcover, hUD, hLip, hnorm⟩ :=
    exists_countable_derivative_cover hD hf (show (0 : ℝ) < ε from hε)
  let P : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hP : ∀ n, MeasurableSet (P n) := fun n =>
    hA.inter (MeasurableSet.disjointed (fun j => (hU j).measurableSet) n)
  have hPA : ∀ n, P n ⊆ A := fun _ => inter_subset_left
  have hPU : ∀ n, P n ⊆ U n := fun n => inter_subset_right.trans (disjointed_subset U n)
  have hdj : Pairwise (Disjoint on P) := fun i j hij =>
    (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have heqA : (⋃ n, P n) = A := by
    dsimp only [P]
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left.mpr (hAD.trans hcover)]
  have hLP : ∀ n, LipschitzOnWith ε f (P n) := by
    intro n
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro a ha b hb
    have hL : (L n : ℝ) ≤ ε := by
      have h := hnorm n a (hPU n ha)
      simpa only [hcrit a (hPA n ha), norm_zero, zero_add] using h
    exact ((hLip n).dist_le_mul a (hPU n ha) b (hPU n hb)).trans
      (mul_le_mul_of_nonneg_right hL (dist_nonneg))
  choose g hg heq using fun n => (hLP n).extend_real
  have hfin : ∀ n, (μH[2] : Measure ℂ) (P n) < ∞ := fun n =>
    (measure_mono (hPA n)).trans_lt hAfin
  choose G hG hbound hint using fun n =>
    exists_exact_lipschitz_length_fiber_majorant (P n) (hfin n) ε (g n) (hg n)
  have heqfiber : ∀ n y, P n ∩ (g n) ⁻¹' {y} = P n ∩ f ⁻¹' {y} := by
    intro n y
    ext x
    by_cases hx : x ∈ P n
    · simp only [mem_inter_iff, hx, true_and, mem_preimage, mem_singleton_iff, ← heq n hx]
    · simp only [mem_inter_iff, hx, false_and]
  refine ⟨fun y => ∑' n, G n y, Measurable.tsum hG, ?_, ?_⟩
  · intro y
    calc
      (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) =
          (μH[1] : Measure ℂ) (⋃ n, P n ∩ f ⁻¹' {y}) := by rw [← iUnion_inter, heqA]
      _ ≤ ∑' n, (μH[1] : Measure ℂ) (P n ∩ f ⁻¹' {y}) := measure_iUnion_le _
      _ ≤ ∑' n, G n y := ENNReal.tsum_le_tsum (fun n => by rw [← heqfiber]; exact hbound n y)
  · rw [lintegral_tsum (fun n => (hG n).aemeasurable)]
    calc
      (∑' n, ∫⁻ y, G n y) ≤ ∑' n, (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) (P n) :=
        ENNReal.tsum_le_tsum hint
      _ = (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) A := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hdj hP, heqA]

lemma ae_zero_critical_fiber_length
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {A : Set ℂ} (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) :
    ∀ᵐ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) = 0 := by
  let ε : ℕ → ℝ≥0 := fun n => ⟨1 / (n + 1 : ℝ), by positivity⟩
  have hε : ∀ n, 0 < ε n := fun n => by change (0 : ℝ) < 1 / (n + 1 : ℝ); positivity
  choose G hG hbound hint using fun n => critical_fiber_majorant hD hf hA hAD hAfin hcrit (ε n) (hε n)
  let H : ℝ → ℝ≥0∞ := fun y => ⨅ n, G n y
  have hH : Measurable H := Measurable.iInf hG
  have hεlim : Tendsto (fun n => (ε n : ℝ≥0∞)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have heq : (fun n => (ε n : ℝ≥0∞)) = fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      funext n
      exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
    rw [heq]
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using h
  have hintH : (∫⁻ y, H y) = 0 := by
    apply le_antisymm _ bot_le
    have ht := ENNReal.Tendsto.mul_const hεlim (Or.inr hAfin.ne)
    simp only [zero_mul] at ht
    apply ge_of_tendsto' ht
    intro n
    exact (lintegral_mono (fun y => iInf_le (fun k => G k y) n)).trans (hint n)
  filter_upwards [(lintegral_eq_zero_iff hH).mp hintH] with y hy
  apply le_antisymm _ bot_le
  change H y = 0 at hy
  exact (le_iInf (fun n => hbound n y)).trans_eq hy

end CircleDomainRigidity

end

end OAI
