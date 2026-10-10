import Mathlib

namespace OAI

universe uX uIota

noncomputable section

namespace Problem326

open Filter Topology

/-- A continuous scalar function on a compact set stays uniformly away from
any value which it never attains. Empty compact sets are allowed. -/
theorem compact_uniform_gap_of_ne
    {X : Type uX} [TopologicalSpace X] {K : Set X} {f : X → ℝ} {t : ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hne : ∀ x ∈ K, f x ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ρ ≤ |f x - t| := by
  apply hK.exists_forall_le' ((hf.sub continuousOn_const).abs)
  intro x hx
  exact abs_pos.mpr (sub_ne_zero.mpr (hne x hx))

/-- The strict conclusions of finitely many closed active-label conditions
extend from one level of a continuous function to a neighborhood of that level.
Each tolerance is fixed separately; no continuity in the label is required. -/
theorem finite_closed_family_extend_fiber
    {X : Type uX} {ι : Type uIota} [TopologicalSpace X] [Finite ι]
    {K : Set X} (hK : IsCompact K)
    (A : ι → Set X) (hA : ∀ i, IsClosed (A i))
    (μ : X → ℝ) (hμ : Continuous μ)
    (error : ι → X → ℝ) (herror : ∀ i, Continuous (error i))
    (E : ι → ℝ) (t : ℝ)
    (hgood : ∀ i x, x ∈ K → x ∈ A i → μ x = t → error i x < E i) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ i x, x ∈ K → x ∈ A i → |μ x - t| < ρ → error i x < E i := by
  let B : Set X := ⋃ i, K ∩ A i ∩ {x | E i ≤ error i x}
  have hB : IsCompact B := by
    apply isCompact_iUnion
    intro i
    exact (hK.inter_right (hA i)).inter_right (isClosed_le continuous_const (herror i))
  have hne : ∀ x ∈ B, μ x ≠ t := by
    intro x hx heq
    rcases Set.mem_iUnion.mp hx with ⟨i, ⟨hxK, hxA⟩, hxerr⟩
    exact (not_le_of_gt (hgood i x hxK hxA heq)) hxerr
  obtain ⟨ρ, hρ, hgap⟩ := compact_uniform_gap_of_ne hB hμ.continuousOn hne
  refine ⟨ρ, hρ, ?_⟩
  intro i x hxK hxA hxgap
  by_contra h
  have hxB : x ∈ B := Set.mem_iUnion.mpr ⟨i, ⟨hxK, hxA⟩, le_of_not_gt h⟩
  exact (not_lt_of_ge (hgap x hxB)) hxgap

/-- Limit points of active parameters as the positive scale tends to zero.
This neighborhood formulation needs no regularity of the activity predicate. -/
def AsymptoticActive {X : Type uX} [PseudoMetricSpace X]
    (active : ℝ → X → Prop) (p : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h < ε ∧
    ∃ q : X, dist q p < ε ∧ active h q

/-- Diagonal closure of asymptotic activity, without assuming continuity of
any scale-dependent affine offset. -/
theorem isClosed_asymptoticActive {X : Type uX} [PseudoMetricSpace X]
    (active : ℝ → X → Prop) : IsClosed {p | AsymptoticActive active p} := by
  apply IsSeqClosed.isClosed
  intro u p hu hup ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hup (ε / 2) (half_pos hε)
  obtain ⟨h, hh, hhε, q, hqu, hactive⟩ := hu n (ε / 2) (half_pos hε)
  refine ⟨h, hh, lt_trans hhε (half_lt_self hε), q, ?_, hactive⟩
  have hnp := hn n le_rfl
  calc dist q p ≤ dist q (u n) + dist (u n) p := dist_triangle _ _ _
       _ < ε := by linarith

/-- An actual convergent active sequence yields asymptotic activity. -/
theorem asymptoticActive_of_sequences {X : Type uX} [PseudoMetricSpace X]
    (active : ℝ → X → Prop) {h : ℕ → ℝ} {q : ℕ → X} {p : X}
    (hhpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hq : Tendsto q atTop (𝓝 p)) (hactive : ∀ n, active (h n) (q n)) :
    AsymptoticActive active p := by
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hq ε hε
  have hevent : ∀ᶠ n in atTop, h n < ε := hh.eventually (gt_mem_nhds hε)
  obtain ⟨m, hm⟩ := eventually_atTop.mp hevent
  let k := max n m
  exact ⟨h k, hhpos k, hm k (le_max_right _ _), q k,
    hn k (le_max_left _ _), hactive k⟩

/-- Every asymptotically active point has a realizing sequence. -/
theorem AsymptoticActive.exists_sequences {X : Type uX} [PseudoMetricSpace X]
    {active : ℝ → X → Prop} {p : X} (hp : AsymptoticActive active p) :
    ∃ (h : ℕ → ℝ) (q : ℕ → X),
      (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧ Tendsto q atTop (𝓝 p) ∧
      ∀ n, active (h n) (q n) := by
  have hδ : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := by
    intro n
    positivity
  choose h hhpos hhδ q hqδ hactive using fun n => hp _ (hδ n)
  have hδlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hhlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => le_of_lt (hhpos n)) (fun n => le_of_lt (hhδ n)) hδlim
  have hqlim : Tendsto q atTop (𝓝 p) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hqδ n)) hδlim
  exact ⟨h, q, hhpos, hhlim, hqlim, hactive⟩

/-- The localization step for arbitrary scale-dependent active families.
Its hypothesis is precisely a strict error bound for every active sequence
whose limit lies in one prescribed level set. -/
theorem active_family_extend_fiber
    {X : Type uX} {ι : Type uIota} [PseudoMetricSpace X] [Finite ι]
    {K : Set X} (hK : IsCompact K)
    (active : ι → ℝ → X → Prop)
    (μ : X → ℝ) (hμ : Continuous μ)
    (error : ι → X → ℝ) (herror : ∀ i, Continuous (error i))
    (E : ι → ℝ) (t : ℝ)
    (hgood : ∀ (i : ι) (h : ℕ → ℝ) (q : ℕ → X) (p : X),
      p ∈ K → μ p = t → (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto q atTop (𝓝 p) → (∀ n, active i (h n) (q n)) → error i p < E i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i p, p ∈ K → |μ p - t| < ρ →
      AsymptoticActive (active i) p → error i p < E i := by
  obtain ⟨ρ, hρ, hlocal⟩ := finite_closed_family_extend_fiber hK
    (fun i => {p | AsymptoticActive (active i) p})
    (fun i => isClosed_asymptoticActive (active i)) μ hμ error herror E t (by
      intro i p hp hactive hlevel
      obtain ⟨h, q, hhpos, hhlim, hqlim, hact⟩ := hactive.exists_sequences
      exact hgood i h q p hp hlevel hhpos hhlim hqlim hact)
  exact ⟨ρ, hρ, fun i p hp hgap hact => hlocal i p hp hact hgap⟩

/-- Compactness turns a strict bound on all limiting active points into a
uniform bound at every sufficiently small positive scale. -/
theorem uniform_activity_of_asymptotic
    {X : Type uX} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    (active : ℝ → X → Prop) (error : X → ℝ) (herror : Continuous error) (E : ℝ)
    (hgood : ∀ p ∈ K, AsymptoticActive active p → error p < E) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∀ p ∈ K, active h p → error p < E := by
  by_contra hfail
  push Not at hfail
  have hw : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < (1 : ℝ) / (n + 1) ∧
      ∃ p ∈ K, active h p ∧ E ≤ error p := by
    intro n
    exact hfail _ (by positivity)
  choose h hhpos hhsmall q hqK hactive hbad using hw
  have hhlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => le_of_lt (hhpos n)) (fun n => le_of_lt (hhsmall n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hpK, φ, hφ, hqφ⟩ := hK.tendsto_subseq hqK
  have hact : AsymptoticActive active p :=
    asymptoticActive_of_sequences active (fun n => hhpos (φ n))
      (hhlim.comp hφ.tendsto_atTop) hqφ (fun n => hactive (φ n))
  have hbadlim : E ≤ error p :=
    ge_of_tendsto (herror.continuousAt.tendsto.comp hqφ)
      (Eventually.of_forall fun n => hbad (φ n))
  exact (not_le_of_gt (hgood p hpK hact)) hbadlim

/-- The scale in the uniform activity estimate can be chosen simultaneously
for finitely many labels. -/
theorem finite_uniform_activity_of_asymptotic
    {X : Type uX} {ι : Type uIota} [PseudoMetricSpace X] [Finite ι]
    {K : Set X} (hK : IsCompact K)
    (active : ι → ℝ → X → Prop) (error : ι → X → ℝ)
    (herror : ∀ i, Continuous (error i)) (E : ι → ℝ)
    (hgood : ∀ i p, p ∈ K → AsymptoticActive (active i) p → error i p < E i) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∀ i p, p ∈ K → active i h p → error i p < E i := by
  choose H hHpos hH using fun i =>
    uniform_activity_of_asymptotic hK (active i) (error i) (herror i) (E i) (hgood i)
  have hHrange : ∀ a ∈ Set.range H, 0 < a := by
    rintro a ⟨i, rfl⟩
    exact hHpos i
  obtain ⟨h0, hh0, hbound⟩ := (Set.finite_range H).isCompact.exists_forall_le'
    continuous_id.continuousOn hHrange
  refine ⟨h0, hh0, ?_⟩
  intro h hhpos hhsmall i p hp hact
  exact hH i h hhpos (lt_of_lt_of_le hhsmall (hbound _ ⟨i, rfl⟩)) p hp hact

end Problem326

end

end OAI
