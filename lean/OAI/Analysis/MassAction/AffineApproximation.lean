import Mathlib

namespace OAI

universe uX uI

/-! Topological compactness tools for the affine-label construction.
These lemmas concern an arbitrary activity relation, so no continuity in the
small parameter or in the label-dependent tolerance is assumed. -/

open Set Filter
open scoped Topology

namespace Problem326.AffineApproximation

variable {X : Type uX} {I : Type uI}

section Topological

variable [TopologicalSpace X]

/-- Points at which a label is active for some positive parameter below `δ`. -/
def smallActivity (A : ℝ → X → I → Prop) (δ : ℝ) (i : I) : Set X :=
  {x | ∃ h : ℝ, 0 < h ∧ h < δ ∧ A h x i}

/-- All limiting activity points as the positive parameter tends to zero. -/
def limitActivity (A : ℝ → X → I → Prop) (i : I) : Set X :=
  ⋂ δ : {δ : ℝ // 0 < δ}, closure (smallActivity A δ i)

theorem isClosed_limitActivity (A : ℝ → X → I → Prop) (i : I) :
    IsClosed (limitActivity A i) :=
  isClosed_iInter fun _ => isClosed_closure

omit [TopologicalSpace X] in
theorem smallActivity_mono (A : ℝ → X → I → Prop) (i : I)
    {δ ε : ℝ} (hδε : δ ≤ ε) : smallActivity A δ i ⊆ smallActivity A ε i := by
  rintro x ⟨h, hh, hδ, hA⟩
  exact ⟨h, hh, hδ.trans_le hδε, hA⟩

/-- A compact set whose limiting activity points all lie in an open set has
uniformly small activity in that open set. -/
theorem uniform_activity_one [T2Space X]
    (A : ℝ → X → I → Prop) (i : I) {K G : Set X}
    (hK : IsCompact K) (hG : IsOpen G)
    (hlim : K ∩ limitActivity A i ⊆ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ x ∈ K, A h x i → x ∈ G := by
  let V : {δ : ℝ // 0 < δ} → Set X :=
    fun δ => K ∩ closure (smallActivity A δ i)
  have hdir : Directed (· ⊇ ·) V := by
    intro δ ε
    refine ⟨⟨min δ.val ε.val, lt_min δ.property ε.property⟩, ?_, ?_⟩
    · exact inter_subset_inter_right K (closure_mono (smallActivity_mono A i (min_le_left _ _)))
    · exact inter_subset_inter_right K (closure_mono (smallActivity_mono A i (min_le_right _ _)))
  have hcpct : ∀ δ, IsCompact (V δ) :=
    fun _ => hK.inter_right isClosed_closure
  have hclosed : ∀ δ, IsClosed (V δ) :=
    fun _ => hK.isClosed.inter isClosed_closure
  have hnhds : ∀ x ∈ ⋂ δ, V δ, G ∈ 𝓝 x := by
    intro x hx
    have hmem : ∀ δ, x ∈ V δ := mem_iInter.mp hx
    apply hG.mem_nhds
    apply hlim
    refine ⟨(hmem ⟨1, zero_lt_one⟩).1, ?_⟩
    exact mem_iInter.mpr fun δ => (hmem δ).2
  have : Nonempty {δ : ℝ // 0 < δ} := ⟨⟨1, zero_lt_one⟩⟩
  obtain ⟨δ, hδ⟩ := exists_subset_nhds_of_isCompact' hdir hcpct hclosed
    (mem_nhdsSet_iff_forall.mpr hnhds)
  refine ⟨δ.val, δ.property, ?_⟩
  intro h hh hsmall x hx hactive
  exact hδ ⟨hx, subset_closure ⟨h, hh, hsmall, hactive⟩⟩

/-- Uniformity holds simultaneously for a finite family of labels. -/
theorem uniform_activity [T2Space X] [Fintype I]
    (A : ℝ → X → I → Prop) {K : Set X} (G : I → Set X)
    (hK : IsCompact K) (hG : ∀ i, IsOpen (G i))
    (hlim : ∀ i, K ∩ limitActivity A i ⊆ G i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ x ∈ K, ∀ i, A h x i → x ∈ G i := by
  classical
  obtain hI | hI := isEmpty_or_nonempty I
  · exact ⟨1, zero_lt_one, fun _ _ _ _ _ i => isEmptyElim i⟩
  · choose δ hδ hbound using fun i => uniform_activity_one A i hK (hG i) (hlim i)
    let δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
    have hδ₀ : 0 < δ₀ := (Finset.lt_inf'_iff _).mpr (fun i _ => hδ i)
    refine ⟨δ₀, hδ₀, ?_⟩
    intro h hh hsmall x hx i hi
    apply hbound i h hh _ x hx hi
    exact hsmall.trans_le (Finset.inf'_le δ (Finset.mem_univ i))

/-- The fixed-minimum guarantee extends to a neighborhood of that minimum.
Only the finitely many fixed tolerance values are used. -/
theorem nearby_level_activity [Finite I]
    (A : ℝ → X → I → Prop) {K : Set X} (hK : IsCompact K)
    (μ : X → ℝ) (hμ : Continuous μ) (t : ℝ)
    (err : I → X → ℝ) (herr : ∀ i, Continuous (err i)) (E : I → ℝ)
    (hgood : ∀ i, ∀ p ∈ K, p ∈ limitActivity A i → μ p = t → err i p < E i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ∀ p ∈ K,
      p ∈ limitActivity A i → |μ p - t| < ρ → err i p < E i := by
  let B : Set X := ⋃ i, K ∩ (limitActivity A i ∩ {p | E i ≤ err i p})
  have hB : IsCompact B := by
    apply isCompact_iUnion
    intro i
    exact hK.inter_right ((isClosed_limitActivity A i).inter
      (isClosed_le continuous_const (herr i)))
  have ht : t ∉ μ '' B := by
    rintro ⟨p, hp, hpt⟩
    obtain ⟨i, hpK, hplim, hpbad⟩ := mem_iUnion.mp hp
    exact (not_lt_of_ge hpbad) (hgood i p hpK hplim hpt)
  have hnhds : (μ '' B)ᶜ ∈ 𝓝 t := (hB.image hμ).isClosed.isOpen_compl.mem_nhds ht
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ρ, hρ, ?_⟩
  intro i p hp hplim hclose
  by_contra hbad
  have hpB : p ∈ B := mem_iUnion.mpr ⟨i, hp, hplim, le_of_not_gt hbad⟩
  have hpball : μ p ∈ Metric.ball t ρ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hclose
  exact (hball hpball) ⟨p, hpB, rfl⟩

end Topological

section Metric

variable [PseudoMetricSpace X]

theorem mem_limitActivity_iff_seq (A : ℝ → X → I → Prop) (i : I) (p : X) :
    p ∈ limitActivity A i ↔
      ∃ h : ℕ → ℝ, ∃ x : ℕ → X,
        (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
        Tendsto x atTop (𝓝 p) ∧ ∀ n, A (h n) (x n) i := by
  constructor
  · intro hp
    have hchoice : ∀ n : ℕ, ∃ x ∈ smallActivity A (1 / ((n : ℝ) + 1)) i,
        dist p x < 1 / ((n : ℝ) + 1) := by
      intro n
      have he : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact Metric.mem_closure_iff.mp (mem_iInter.mp hp ⟨_, he⟩) _ he
    choose x hx hdist using hchoice
    choose h hpos hsmall hA using hx
    refine ⟨h, x, hpos, ?_, ?_, hA⟩
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat
        (fun n => (hpos n).le) (fun n => (hsmall n).le)
    · apply tendsto_iff_dist_tendsto_zero.mpr
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat
      · intro n
        exact dist_nonneg
      · intro n
        simpa only [dist_comm] using (hdist n).le
  · rintro ⟨h, x, hpos, hh, hx, hA⟩
    apply mem_iInter.mpr
    intro δ
    apply isClosed_closure.mem_of_tendsto hx
    filter_upwards [hh.eventually_lt_const δ.property] with n hn
    exact subset_closure ⟨h n, hpos n, hn, hA n⟩

/-- Uniform activity bound in exactly the sequential form used by the affine
approximation lemma. -/
theorem uniform_activity_of_sequence [T2Space X] [Fintype I]
    (A : ℝ → X → I → Prop) {K : Set X} (hK : IsCompact K)
    (err : I → X → ℝ) (herr : ∀ i, Continuous (err i)) (E : I → ℝ)
    (hseq : ∀ i, ∀ p ∈ K, ∀ h : ℕ → ℝ, ∀ x : ℕ → X,
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) → Tendsto x atTop (𝓝 p) →
      (∀ n, A (h n) (x n) i) → err i p < E i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, ∀ i, A h p i → err i p < E i := by
  apply uniform_activity A (fun i => {p | err i p < E i}) hK
  · intro i
    exact isOpen_lt (herr i) continuous_const
  · intro i p hp
    obtain ⟨h, x, hpos, hh, hx, hA⟩ := (mem_limitActivity_iff_seq A i p).mp hp.2
    exact hseq i p hp.1 h x hpos hh hx hA

end Metric

end Problem326.AffineApproximation

end OAI
