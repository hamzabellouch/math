import Mathlib

namespace OAI

universe uX uIota

open Set Filter
open scoped Topology

namespace Problem326

/-- Limiting points of activity as the positive parameter tends to zero,
expressed using closed sets; no continuity of `active` is required. -/
def activityLimitSet {X : Type uX} [TopologicalSpace X]
    (active : ℝ → X → Prop) : Set X :=
  ⋂ n : ℕ, closure {p | ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧ active h p}

theorem isClosed_activityLimitSet {X : Type uX} [TopologicalSpace X]
    (active : ℝ → X → Prop) : IsClosed (activityLimitSet active) :=
  isClosed_iInter (fun _ => isClosed_closure)

/-- Every limit of active points at positive parameters tending to zero
belongs to the closed activity-limit set. -/
theorem mem_activityLimitSet_of_tendsto
    {X : Type uX} [TopologicalSpace X] {active : ℝ → X → Prop}
    {h : ℕ → ℝ} {p : ℕ → X} {z : X}
    (hhpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 z)) (ha : ∀ n, active (h n) (p n)) :
    z ∈ activityLimitSet active := by
  apply mem_iInter.mpr
  intro n
  apply isClosed_closure.mem_of_tendsto hp
  have hev : ∀ᶠ k in atTop, h k < 1 / ((n : ℝ) + 1) :=
    hh.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hev] with k hk
  exact subset_closure ⟨h k, hhpos k, hk, ha k⟩

/-- In a pseudometric space every point of the activity-limit set is realized
by an actual sequence, even when activity is not a closed relation. -/
theorem exists_active_sequence_of_mem_activityLimitSet
    {X : Type uX} [PseudoMetricSpace X] {active : ℝ → X → Prop} {z : X}
    (hz : z ∈ activityLimitSet active) :
    ∃ (h : ℕ → ℝ) (p : ℕ → X), (∀ n, 0 < h n) ∧
      Tendsto h atTop (𝓝 0) ∧ Tendsto p atTop (𝓝 z) ∧
      ∀ n, active (h n) (p n) := by
  classical
  have hex (n : ℕ) : ∃ p, (∃ h : ℝ, 0 < h ∧
      h < 1 / ((n : ℝ) + 1) ∧ active h p) ∧
      dist z p < 1 / ((n : ℝ) + 1) :=
    Metric.mem_closure_iff.mp (mem_iInter.mp hz n)
      (1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp hdist using hex
  choose h hhpos hhsmall ha using hp
  refine ⟨h, p, hhpos, ?_, ?_, ha⟩
  · exact squeeze_zero (fun n => (hhpos n).le) (fun n => (hhsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [dist_comm] using (hdist n).le

/-- Compactness upgrades avoidance of one level to a positive uniform gap. -/
theorem compact_avoid_level_has_uniform_gap
    {X : Type uX} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : ContinuousOn f K) (t : ℝ)
    (hne : ∀ x ∈ K, f x ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ρ ≤ |f x - t| := by
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · exact ⟨1, zero_lt_one, by simp [hEmpty]⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hNonempty
      ((hf.sub continuousOn_const).abs)
    exact ⟨|f x - t|, abs_pos.mpr (sub_ne_zero.mpr (hne x hx)), hmin⟩

/-- A good-label guarantee at one level extends to nearby levels. This is the
compact bad-limit-set argument; tolerances may vary arbitrarily between labels. -/
theorem activity_limits_good_near_level
    {X : Type uX} [TopologicalSpace X] {ι : Type uIota} [Finite ι]
    {K : Set X} (hK : IsCompact K) (active : ι → ℝ → X → Prop)
    (good : ι → Set X) (hgood : ∀ i, IsOpen (good i))
    {f : X → ℝ} (hf : ContinuousOn f K) (t : ℝ)
    (hlevel : ∀ i z, z ∈ K → f z = t →
      z ∈ activityLimitSet (active i) → z ∈ good i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ K, |f z - t| < ρ →
      ∀ i, z ∈ activityLimitSet (active i) → z ∈ good i := by
  classical
  let B : Set X := K ∩ ⋃ i, activityLimitSet (active i) ∩ (good i)ᶜ
  have hB : IsCompact B := hK.inter_right
    (isClosed_iUnion_of_finite (fun i =>
      (isClosed_activityLimitSet (active i)).inter (hgood i).isClosed_compl))
  have hne : ∀ z ∈ B, f z ≠ t := by
    intro z hz heq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz.2
    exact hi.2 (hlevel i z hz.1 heq hi.1)
  obtain ⟨ρ, hρ, hgap⟩ := compact_avoid_level_has_uniform_gap hB
    (hf.mono inter_subset_left) t hne
  refine ⟨ρ, hρ, ?_⟩
  intro z hz hnear i ha
  by_contra hbad
  exact (not_le_of_gt hnear) (hgap z ⟨hz, mem_iUnion.mpr ⟨i, ha, hbad⟩⟩)

end Problem326

end OAI
