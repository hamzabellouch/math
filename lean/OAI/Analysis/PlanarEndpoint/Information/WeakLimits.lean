import Mathlib

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace PlanarEndpoint.TransverseInformation

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

lemma open_null_of_weak_limit {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {G : Set Ω} (hG : IsOpen G)
    (h0 : Tendsto (fun n => (μs n : Measure Ω) G) atTop (𝓝 0)) :
    (μ : Measure Ω) G = 0 := by
  apply le_antisymm _ bot_le
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG
  rw [h0.liminf_eq] at h
  exact h

lemma open_null_of_weak_limit_bound {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {G : Set Ω} (hG : IsOpen G) {ε : ℕ → ℝ≥0∞}
    (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, (μs n : Measure Ω) G ≤ ε n) :
    (μ : Measure Ω) G = 0 := by
  apply open_null_of_weak_limit hμ hG
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hε
    (Eventually.of_forall (fun _ => bot_le)) hb

lemma ae_nonneg_of_weak_limit_tails {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {d : Ω → ℝ} (hd : Continuous d)
    (htail : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (μs n : Measure Ω) {x | d x < -η}) atTop (𝓝 0)) :
    ∀ᵐ x ∂(μ : Measure Ω), 0 ≤ d x := by
  have ha : ∀ q : ℚ, ∀ᵐ x ∂(μ : Measure Ω),
      0 < (q : ℝ) → -(q : ℝ) ≤ d x := by
    intro q
    by_cases hq : 0 < (q : ℝ)
    · have hnull := open_null_of_weak_limit hμ
        (isOpen_lt hd continuous_const) (htail q hq)
      have hb : ∀ᵐ x ∂(μ : Measure Ω), -(q : ℝ) ≤ d x := by
        apply ae_iff.mpr
        simpa only [not_le] using hnull
      exact hb.mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [ae_all_iff.mpr ha] with x hx
  by_contra hn
  have hneg : d x < 0 := lt_of_not_ge hn
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (neg_pos.mpr hneg)
  have h := hx q hq0
  linarith

lemma ae_le_on_open_of_weak_limit_tails {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {G : Set Ω} (hG : IsOpen G) {d : Ω → ℝ} (hd : Continuous d) (γ : ℝ)
    (htail : ∀ η : ℝ, 0 < η → Tendsto
      (fun n => (μs n : Measure Ω) (G ∩ {x | γ + η < d x})) atTop (𝓝 0)) :
    ∀ᵐ x ∂(μ : Measure Ω), x ∈ G → d x ≤ γ := by
  have ha : ∀ q : ℚ, ∀ᵐ x ∂(μ : Measure Ω),
      0 < (q : ℝ) → x ∈ G → d x ≤ γ + q := by
    intro q
    by_cases hq : 0 < (q : ℝ)
    · have hnull := open_null_of_weak_limit hμ
        (hG.inter (isOpen_lt continuous_const hd)) (htail q hq)
      have hb : ∀ᵐ x ∂(μ : Measure Ω), x ∈ G → d x ≤ γ + q := by
        apply ae_iff.mpr
        change (μ : Measure Ω) {x | x ∈ G ∧ γ + (q : ℝ) < d x} = 0 at hnull
        simpa only [not_forall, not_le, exists_prop] using hnull
      exact hb.mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [ae_all_iff.mpr ha] with x hx
  intro hxG
  by_contra hn
  have hpos : 0 < d x - γ := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn hpos
  have h := hx q hq0 hxG
  linarith

lemma open_positive_persists {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {G : Set Ω} (hG : IsOpen G) {a : ℝ≥0∞} (ha : a < (μ : Measure Ω) G) :
    ∀ᶠ n in atTop, a < (μs n : Measure Ω) G := by
  exact Filter.eventually_lt_of_lt_liminf
    (ha.trans_le (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG))

lemma ae_eq_of_weak_limit {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {a b : Ω → ℝ} (ha : Continuous a) (hb : Continuous b)
    (heq : ∀ n, a =ᵐ[(μs n : Measure Ω)] b) :
    a =ᵐ[(μ : Measure Ω)] b := by
  apply ae_iff.mpr
  apply open_null_of_weak_limit hμ (isOpen_ne_fun ha hb)
  have hz : ∀ n, (μs n : Measure Ω) {x | ¬a x = b x} = 0 :=
    fun n => ae_iff.mp (heq n)
  simp only [hz]
  exact tendsto_const_nhds

end PlanarEndpoint.TransverseInformation
end

end OAI
