import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListFullDegree

namespace OAI

/-! Bounded initial star lengths suffice for degree three after a fixed number
of literal fork rounds. This statement concerns the actual emitted bond list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem next_ordinary_noLoops (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) :
    ∀ b ∈ (next N s).2.1, b.1 ≠ b.2.1 := by
  intro b hm
  change b ∈ s.2.1++addedBonds s (scale N s) at hm
  rcases List.mem_append.mp hm with ho | ha
  · exact hn b ho
  · exact (addedBonds_valid s hs (scale N s) b ha).2.2

theorem iterate_ordinary_noLoops (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (k : ℕ) :
    ∀ b ∈ (iterate N k s).2.1, b.1 ≠ b.2.1 := by
  induction k with
  | zero => exact hn
  | succ k ih => exact next_ordinary_noLoops N _ (iterate_validPorts N s hs k) ih

theorem iterate_full_degree_le_three (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s)
    (D : ℕ) (hD : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D)
    (v : Fin (iterate N D s).1) :
    degree ((iterate N D s).2.1++activeBonds (iterate N D s).2.2.2) v.val ≤ 3 := by
  apply full_degree_le_three _ (iterate_validPorts N s hs D)
    (iterate_ordinary_bounded N s hs hb D) (iterate_ordinary_noLoops N s hs hn D)
    (iterate_degreeBounds N s hs hb hd D) _ v
  intro i
  have hi : i.val<s.2.2.2.length := by simpa only [iterate_centers] using i.isLt
  rw [iterate_group_length N s D i.val hi]
  exact (qmaForkDegreeAfter_constant _ D (hD ⟨i.val,hi⟩)).trans (by decide)

theorem initial_ordinary_noLoops (n : ℕ) (bs : List Bond) (c N : ℚ) :
    ∀ b ∈ (initial n bs c N).2.1, b.1 ≠ b.2.1 := by
  intro b hb
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hb
  dsimp only
  omega

theorem initial_iterate_full_degree_le_three (n : ℕ) (bs : List Bond) (c N : ℚ)
    (D : ℕ) (hD : ∀ i : Fin n, (initialIndices bs i.val).length ≤ D)
    (v : Fin (iterate N D (initial n bs c N)).1) :
    degree ((iterate N D (initial n bs c N)).2.1++
      activeBonds (iterate N D (initial n bs c N)).2.2.2) v.val ≤ 3 := by
  apply iterate_full_degree_le_three N _ (initial_validPorts n bs c N)
    (initial_ordinary_bounded n bs c N) (initial_ordinary_noLoops n bs c N)
    (initial_degreeBounds n bs c N) D _ v
  intro i
  have hi : i.val<n := by simpa only [initial,List.length_map,List.length_range] using i.isLt
  change (groupAt ((List.range n).map (initialGroup n bs (initialScale N bs c))) i.val).length ≤ D
  rw [initial_groupAt n bs (initialScale N bs c) i.val hi]
  simpa only [initialGroup,List.length_map] using hD ⟨i.val,hi⟩

theorem initialIndices_length_eq_degree (bs : List Bond)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (i : ℕ) :
    (initialIndices bs i).length=degree bs i := by
  have hone (xs : List ℕ) : (xs.map (fun _ => (1:ℕ))).sum=xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
      omega
  rw [← hone (initialIndices bs i),initialIndices_sum,initial_evenodd_sum]
  simp only [initialEndpoint_even,initialEndpoint_odd]
  unfold degree
  rw [initial_list_sum]
  unfold incident
  apply Finset.sum_congr rfl
  intro e _
  have he := hn (bs.get e) (List.get_mem bs e)
  simp only [List.get_eq_getElem] at he ⊢
  split_ifs <;> omega

theorem initial_iterate_full_degree_of_bound (n : ℕ) (bs : List Bond)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (c N : ℚ) (D : ℕ)
    (hD : ∀ i : Fin n, degree bs i.val ≤ D)
    (v : Fin (iterate N D (initial n bs c N)).1) :
    degree ((iterate N D (initial n bs c N)).2.1++
      activeBonds (iterate N D (initial n bs c N)).2.2.2) v.val ≤ 3 := by
  apply initial_iterate_full_degree_le_three n bs c N D _ v
  intro i
  rw [initialIndices_length_eq_degree bs hn]
  exact hD i

end ContinuumCoulomb.QuantumForkList

end

end OAI
