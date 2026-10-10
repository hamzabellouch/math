import OAI.Computability.LoopMatching.Model
import OAI.Computability.LoopMatching.CountDecomposition

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

def recordedVertices (G : Input) : Finset ℕ :=
  (G.ordinary.records.map BinaryMatching.Record.left ++
    G.ordinary.records.map BinaryMatching.Record.right ++
    G.loops.map LoopRecord.vertex).toFinset

theorem recordedVertices_card_le (G : Input) :
    (recordedVertices G).card ≤ 2 * G.ordinary.records.length + G.loops.length := by
  have h := List.toFinset_card_le (G.ordinary.records.map BinaryMatching.Record.left ++
    G.ordinary.records.map BinaryMatching.Record.right ++
    G.loops.map LoopRecord.vertex)
  simpa only [recordedVertices, List.length_append, List.length_map, two_mul] using h

theorem ordinary_endpoints_mem_recordedVertices (G : Input)
    (e : BinaryMatching.Pair G.n) (he : BinaryMatching.multiplicity G.ordinary e ≠ 0) :
    e.val.1.val ∈ recordedVertices G ∧ e.val.2.val ∈ recordedVertices G := by
  unfold BinaryMatching.multiplicity at he
  cases hf : G.ordinary.records.find?
      (fun r => r.left = e.val.1.val && r.right = e.val.2.val) with
  | none => simp only [hf] at he; exact (he rfl).elim
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    constructor
    · have hm : e.val.1.val ∈ G.ordinary.records.map BinaryMatching.Record.left :=
        List.mem_map.mpr ⟨r, hr, hp.1⟩
      simp only [recordedVertices, List.mem_toFinset, List.mem_append]
      exact Or.inl (Or.inl hm)
    · have hm : e.val.2.val ∈ G.ordinary.records.map BinaryMatching.Record.right :=
        List.mem_map.mpr ⟨r, hr, hp.2⟩
      simp only [recordedVertices, List.mem_toFinset, List.mem_append]
      exact Or.inl (Or.inr hm)

theorem loop_mem_recordedVertices (G : Input) (v : Fin G.n)
    (hv : loopMultiplicity G v ≠ 0) : v.val ∈ recordedVertices G := by
  unfold loopMultiplicity at hv
  cases hf : G.loops.find? (fun r => r.vertex == v.val) with
  | none => simp only [hf] at hv; exact (hv rfl).elim
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have heq : r.vertex = v.val := by simpa using hp
    have hm : v.val ∈ G.loops.map LoopRecord.vertex := List.mem_map.mpr ⟨r, hr, heq⟩
    simp only [recordedVertices, List.mem_toFinset, List.mem_append]
    exact Or.inr hm

theorem range_subset_recordedVertices_of_weight_ne_zero (G : Input)
    (M : PartialMatching G.n) (hM : weight G M ≠ 0) :
    Finset.range G.n ⊆ recordedVertices G := by
  classical
  intro x hx
  let v : Fin G.n := ⟨x, Finset.mem_range.mp hx⟩
  by_cases hloop : v ∈ loopVertices M
  · have hn : loopMultiplicity G v ≠ 0 := by
      intro hz
      exact hM (weight_eq_zero_of_loopMultiplicity_eq_zero G M v hloop hz)
    exact loop_mem_recordedVertices G v hn
  · have hex : ∃ e ∈ M.val, (BinaryMatching.completeGraph G.n).Incident v e := by
      simpa only [loopVertices, Finset.mem_filter, Finset.mem_univ, true_and,
        not_forall, not_not, exists_prop] using hloop
    obtain ⟨e, he, hi⟩ := hex
    have hn : BinaryMatching.multiplicity G.ordinary e ≠ 0 := by
      intro hz
      exact hM (weight_eq_zero_of_multiplicity_eq_zero G M e he hz)
    have hep := ordinary_endpoints_mem_recordedVertices G e hn
    change e.val.1 = v ∨ e.val.2 = v at hi
    rcases hi with hi | hi
    · simpa only [hi] using hep.1
    · simpa only [hi] using hep.2

theorem vertex_bound_of_weight_ne_zero (G : Input) (M : PartialMatching G.n)
    (hM : weight G M ≠ 0) :
    G.n ≤ 2 * G.ordinary.records.length + G.loops.length := by
  have h := Finset.card_le_card (range_subset_recordedVertices_of_weight_ne_zero G M hM)
  rw [Finset.card_range] at h
  exact h.trans (recordedVertices_card_le G)

theorem count_eq_zero_of_sparse_bound (G : Input)
    (h : 2 * G.ordinary.records.length + G.loops.length < G.n) : count G = 0 := by
  apply count_eq_zero_of_forall_weight_eq_zero
  intro M
  by_contra hM
  exact (Nat.not_le_of_gt h) (vertex_bound_of_weight_ne_zero G M hM)

theorem vertex_bound_of_count_ne_zero (G : Input) (h : count G ≠ 0) :
    G.n ≤ 2 * G.ordinary.records.length + G.loops.length := by
  by_contra hb
  exact h (count_eq_zero_of_sparse_bound G (Nat.lt_of_not_ge hb))

end LoopMatching

end OAI
