import Mathlib

namespace OAI

universe uX uIota

open Set Filter Topology

namespace Problem326

/-! Topological support for the local-to-global affine-label construction.
The parameter approaches zero through positive values; no continuity in that
parameter is assumed. -/

variable {X : Type uX} [TopologicalSpace X]

/-- Limit points of a state family as a positive real parameter tends to zero. -/
def positiveLimitSet (A : ℝ → Set X) : Set X :=
  {p | (0, p) ∈ closure {u : ℝ × X | 0 < u.1 ∧ u.2 ∈ A u.1}}

theorem isClosed_positiveLimitSet (A : ℝ → Set X) :
    IsClosed (positiveLimitSet A) := by
  exact isClosed_closure.preimage (continuous_const.prodMk continuous_id)

theorem mem_positiveLimitSet_of_tendsto {A : ℝ → Set X}
    {h : ℕ → ℝ} {q : ℕ → X} {p : X}
    (hh : Tendsto h atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 p))
    (hpos : ∀ n, 0 < h n) (hmem : ∀ n, q n ∈ A (h n)) :
    p ∈ positiveLimitSet A := by
  exact isClosed_closure.mem_of_tendsto (hh.prodMk_nhds hq)
    (Eventually.of_forall fun n => subset_closure ⟨hpos n, hmem n⟩)

theorem mem_positiveLimitSet_iff_seq [FirstCountableTopology X]
    {A : ℝ → Set X} {p : X} :
    p ∈ positiveLimitSet A ↔
      ∃ (h : ℕ → ℝ) (q : ℕ → X),
        Tendsto h atTop (𝓝 0) ∧ Tendsto q atTop (𝓝 p) ∧
        (∀ n, 0 < h n) ∧ (∀ n, q n ∈ A (h n)) := by
  constructor
  · intro hp
    obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hp
    exact ⟨fun n => (u n).1, fun n => (u n).2,
      ht.fst_nhds, ht.snd_nhds,
      fun n => (hu n).1, fun n => (hu n).2⟩
  · rintro ⟨h, q, hh, hq, hpos, hmem⟩
    exact mem_positiveLimitSet_of_tendsto hh hq hpos hmem

theorem isCompact_positiveLimitSet_inter {A : ℝ → Set X} {K : Set X}
    (hK : IsCompact K) : IsCompact (positiveLimitSet A ∩ K) := by
  exact hK.inter_left (isClosed_positiveLimitSet A)

/-- A compact set missing a level of a continuous scalar function misses a
whole open band around that level. This also handles an empty compact set. -/
theorem exists_pos_band_disjoint {K : Set X} (hK : IsCompact K)
    {μ : X → ℝ} (hμ : ContinuousOn μ K) {t : ℝ}
    (havoid : ∀ p ∈ K, μ p ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ K, ρ ≤ |μ p - t| := by
  apply hK.exists_forall_le' ((hμ.sub continuousOn_const).abs)
  intro p hp
  exact abs_pos.mpr (sub_ne_zero.mpr (havoid p hp))

/-- The finite-family form of the neighborhood extension step. If every
limiting active label is good at one level, then this also holds in a band
around that level. The good sets are open, but the active sets may be arbitrary. -/
theorem exists_pos_band_of_limit_good {ι : Type uIota} [Finite ι]
    {K : Set X} (hK : IsCompact K) {μ : X → ℝ}
    (hμ : ContinuousOn μ K) {t : ℝ} (A : ι → ℝ → Set X)
    (G : ι → Set X) (hG : ∀ i, IsOpen (G i))
    (hgood : ∀ i p, p ∈ K → μ p = t →
      p ∈ positiveLimitSet (A i) → p ∈ G i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i p, p ∈ K → |μ p - t| < ρ →
      p ∈ positiveLimitSet (A i) → p ∈ G i := by
  let B : Set X := ⋃ i, (positiveLimitSet (A i) ∩ K) \ G i
  have hBc : IsCompact B := by
    apply isCompact_iUnion
    intro i
    exact (isCompact_positiveLimitSet_inter hK).diff (hG i)
  have hBK : B ⊆ K := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hi.1.2
  have havoid : ∀ p ∈ B, μ p ≠ t := by
    intro p hp heq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hi.2 (hgood i p hi.1.2 heq hi.1.1)
  obtain ⟨ρ, hρ, hsep⟩ := exists_pos_band_disjoint hBc (hμ.mono hBK) havoid
  refine ⟨ρ, hρ, ?_⟩
  intro i p hp hband hlim
  by_contra hbad
  have hpB : p ∈ B := mem_iUnion.mpr ⟨i, ⟨⟨hlim, hp⟩, hbad⟩⟩
  exact (not_lt_of_ge (hsep p hpB)) hband

/-- Compactness upgrades a limiting active-set inclusion into a uniform
small-parameter inclusion. No continuity of the active sets is required. -/
theorem exists_pos_uniform_of_limit_subset [FirstCountableTopology X]
    {A : ℝ → Set X} {K G : Set X} (hK : IsCompact K) (hG : IsOpen G)
    (hgood : ∀ p ∈ K, p ∈ positiveLimitSet A → p ∈ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, p ∈ A h → p ∈ G := by
  classical
  by_contra! hn
  have hex : ∀ n : ℕ, ∃ (h : ℝ) (p : X),
      0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧ p ∈ K ∧ p ∈ A h ∧ p ∉ G := by
    intro n
    obtain ⟨h, hh, hsmall, p, hpK, hpA, hpG⟩ :=
      hn (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨h, p, hh, hsmall, hpK, hpA, hpG⟩
  choose h q hpos hsmall hqK hqA hqG using hex
  have ht : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hpos n).le) (fun n => (hsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hpK, φ, hφ, hq⟩ := hK.tendsto_subseq hqK
  have hlim : p ∈ positiveLimitSet A :=
    mem_positiveLimitSet_of_tendsto (ht.comp hφ.tendsto_atTop) hq
      (fun n => hpos (φ n)) (fun n => hqA (φ n))
  have hbad : p ∈ Gᶜ := hG.isClosed_compl.mem_of_tendsto hq
    (Eventually.of_forall fun n => hqG (φ n))
  exact hbad (hgood p hpK hlim)

/-- Uniform small-parameter inclusion for any finite family of active sets. -/
theorem exists_pos_uniform_of_finite_limit_subset [FirstCountableTopology X]
    {ι : Type uIota} [Finite ι] {A : ι → ℝ → Set X} {K : Set X}
    {G : ι → Set X} (hK : IsCompact K) (hG : ∀ i, IsOpen (G i))
    (hgood : ∀ i p, p ∈ K → p ∈ positiveLimitSet (A i) → p ∈ G i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ i p, p ∈ K → p ∈ A i h → p ∈ G i := by
  classical
  have hex := fun i => exists_pos_uniform_of_limit_subset hK (hG i) (hgood i)
  choose δ hδ hδgood using hex
  have hcompact : IsCompact (Set.range δ) := (Set.finite_range δ).isCompact
  obtain ⟨δ₀, hδ₀, hmin⟩ := hcompact.exists_forall_le' continuousOn_id
    (show ∀ y ∈ Set.range δ, (0 : ℝ) < y from by
      rintro y ⟨i, rfl⟩
      exact hδ i)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro h hh hsmall i p hp hactive
  exact hδgood i h hh (lt_of_lt_of_le hsmall (hmin (δ i) ⟨i, rfl⟩))
    p hp hactive

end Problem326

end OAI
