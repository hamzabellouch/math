import OAI.Combinatorics.MatchingEntropy.Components

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem empty_conventions (G : LooplessGraph V E) (hV : Fintype.card V = 0) :
    Fintype.card E = 0 ∧ Fintype.card G.Matching = 1 ∧ G.polytope = {0} ∧
    (∀ x ∈ G.polytope, entropy x = 0 ∧ complementEntropy x = 0 ∧ maxMatchingEntropy G x = 0) ∧
    (∀ β : E → ℝ, weightedPartition G β = 1 ∧ weightedObjective β 0 = 0) ∧
    (∀ k : ℕ, 1 ≤ k → (Real.exp (-2) * (k : ℝ))^0 = 1) := by
  have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
  have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
  let M : G.Matching := ⟨∅,fun v => isEmptyElim v⟩
  have : Nonempty G.Matching := ⟨M⟩
  have : Subsingleton G.Matching := inferInstance
  have hc : Fintype.card G.Matching = 1 := by
    let : Unique G.Matching := ⟨⟨M⟩, fun _ => Subsingleton.elim _ _⟩
    exact Fintype.card_unique
  have hi : G.indicator M = 0 := Subsingleton.elim _ _
  have hp : G.polytope = {0} := by
    apply Set.Subset.antisymm
    · intro x _
      exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
    · rintro x rfl
      rw [← hi]
      exact subset_convexHull ℝ _ (Set.mem_range_self M)
  refine ⟨Fintype.card_eq_zero, hc, hp, ?_, ?_, fun _ _ => pow_zero _⟩
  · intro x hx
    have hF : entropy x = 0 := by simp [entropy]
    have hB : complementEntropy x = 0 := by simp [complementEntropy, entropy]
    refine ⟨hF,hB,le_antisymm ?_ (maxMatchingEntropy_nonneg G hx)⟩
    simpa [hF] using refined_upper G x hx
  · intro β
    constructor
    · simp [weightedPartition, hc]
    · simp [weightedObjective, entropy]

theorem no_matching_polytope {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) :
    IsEmpty G.Matching ↔ G.polytope = ∅ := by
  constructor
  · intro hm
    have : IsEmpty G.Matching := hm
    exact Set.eq_empty_iff_forall_notMem.mpr (fun x hx => by
      obtain ⟨M⟩ := matching_nonempty_of_mem G hx
      exact isEmptyElim M)
  · intro hp
    exact ⟨fun M => by
      have h := subset_convexHull ℝ (Set.range G.indicator) (Set.mem_range_self M)
      change G.indicator M ∈ G.polytope at h
      rw [hp] at h
      exact h⟩

theorem zero_selected_bound {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (m : ℕ) (hm : 0 < m) :
    (Real.exp (-2) * (0 : ℝ))^m = 0 ∧ (0 : ℝ) ≤ Fintype.card G.Matching := by
  simp [zero_pow (Nat.ne_of_gt hm)]

theorem zero_regular {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (hV : 0 < Fintype.card V)
    (hreg : ∀ v, (Finset.univ.filter (G.Incident v)).card = 0) :
    Fintype.card E = 0 ∧ IsEmpty G.Matching := by
  have he : IsEmpty E := by
    refine ⟨fun e => ?_⟩
    have hh := Finset.card_eq_zero.mp (hreg (G.left e))
    have hm : e ∈ Finset.univ.filter (G.Incident (G.left e)) := by
      simp [LooplessGraph.Incident]
    rw [hh] at hm
    exact Finset.notMem_empty e hm
  have : IsEmpty E := he
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV
  exact ⟨Fintype.card_eq_zero, ⟨fun M => by obtain ⟨e,_,_⟩ := M.property v; exact isEmptyElim e⟩⟩

theorem one_selected_bound {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (M : G.Matching) :
    1 ≤ Fintype.card G.Matching := Fintype.card_pos_iff.mpr ⟨M⟩

theorem one_partition_exact {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (M : G.Matching)
    (hcover : M.val = Finset.univ) : Fintype.card G.Matching = 1 := by
  have hu : ∀ N : G.Matching, N = M := by
    intro N
    apply Subtype.ext
    apply Finset.Subset.antisymm
    · rw [hcover]
      exact Finset.subset_univ _
    · intro e he
      obtain ⟨f,hf,_⟩ := N.property (G.left e)
      have hfm : f ∈ M.val := hcover ▸ Finset.mem_univ f
      have hfe := (M.property (G.left e)).unique ⟨hfm,hf.2⟩ ⟨he,Or.inl rfl⟩
      exact hfe ▸ hf.1
  have : Subsingleton G.Matching := ⟨fun a b => (hu a).trans (hu b).symm⟩
  exact by
    let : Unique G.Matching := ⟨⟨M⟩, fun _ => Subsingleton.elim _ _⟩
    exact Fintype.card_unique

theorem pointwise_endpoints (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    entropy x - 2 * complementEntropy x ≤ maxMatchingEntropy G x ∧
      (m = 1 → maxMatchingEntropy G x = entropy x) := by
  have hl := refined_lower G m hm hV x hx
  change entropy x - (2 - 2 / (m : ℝ)) * complementEntropy x ≤ maxMatchingEntropy G x at hl
  have hB := B_nonneg G hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · have hpos := mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hmR.le) hB
    nlinarith
  · intro hh
    subst m
    norm_num at hl
    exact le_antisymm (refined_upper G x hx) hl

end MatchingEntropyBounds.Refined

end

end OAI
