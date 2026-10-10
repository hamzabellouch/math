import OAI.Analysis.CircleDomains.Sobolev.DifferentiableCriticalPieces
import OAI.Analysis.CircleDomains.Sobolev.LipschitzLengthFiberMajorant
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! Critical differentiability points contribute zero length on almost every
scalar fiber. No continuity of the differential is used. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_critical_fiber_majorant
    {f : ℂ → ℝ} {A : Set ℂ} (hA : MeasurableSet A)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hd : ∀ x ∈ A, DifferentiableAt ℝ f x)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) A := by
  rcases A.eq_empty_or_nonempty with h0 | hn
  · subst A
    exact ⟨0, measurable_const, by simp, by simp⟩
  obtain ⟨P,hP,hdj,heqA,hLP⟩ := differentiable_critical_pieces hA hn hd hcrit ε hε
  have hPA (n : ℕ) : P n ⊆ A := by rw [← heqA]; exact subset_iUnion P n
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

lemma ae_zero_differentiable_critical_fiber_length
    {f : ℂ → ℝ} {A : Set ℂ} (hA : MeasurableSet A)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hd : ∀ x ∈ A, DifferentiableAt ℝ f x)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) :
    ∀ᵐ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) = 0 := by
  let ε : ℕ → ℝ≥0 := fun n => ⟨1 / (n + 1 : ℝ), by positivity⟩
  have hε : ∀ n, 0 < ε n := fun n => by change (0 : ℝ) < 1 / (n + 1 : ℝ); positivity
  choose G hG hbound hint using fun n => differentiable_critical_fiber_majorant hA hAfin hd hcrit (ε n) (hε n)
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
