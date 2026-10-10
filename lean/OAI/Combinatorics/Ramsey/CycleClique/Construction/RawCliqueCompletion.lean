import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPathSystem

namespace OAI

/-! Include every unused clique vertex as a singleton chain. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

noncomputable def completeClique (S : RawPathSystem G Q) : RawPathSystem G Q := by
  classical
  let U := Q \ S.vertices
  refine {
    chains := S.chains ++ U.toList.map (fun v => [v])
    paths := ?_
    disjoint := ?_
    endpoints := ?_
    no_clique_steps := ?_ }
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.paths l hl
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact ⟨by simp, .singleton v⟩
  · apply List.pairwise_append.mpr
    refine ⟨S.disjoint, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      apply U.nodup_toList.imp
      intro v w hne
      simpa using hne.symm
    · intro l hl m hm
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
      apply List.disjoint_left.mpr
      intro w hw hwv
      have heq : w = v := by simpa using hwv
      subst w
      have hvU : v ∈ U := Finset.mem_toList.mp hv
      exact (Finset.mem_sdiff.mp hvU).2
        (List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hl, hw⟩))
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.endpoints l hl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      have hvQ : v ∈ Q := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1
      simpa using And.intro hvQ hvQ
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.no_clique_steps l hl
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact .singleton v

theorem completeClique_vertices (S : RawPathSystem G Q) :
    S.completeClique.vertices = S.vertices ∪ Q := by
  classical
  ext v
  simp [vertices, completeClique]
  by_cases hv : ∃ l ∈ S.chains, v ∈ l <;> simp_all

@[simp] theorem completeClique_amount (S : RawPathSystem G Q) :
    S.completeClique.amount = S.amount := by
  classical
  unfold amount
  rw [completeClique_vertices, Finset.union_sdiff_distrib]
  simp

@[simp] theorem completeClique_assignedCount (S : RawPathSystem G Q) :
    S.completeClique.assignedCount = S.assignedCount := by
  classical
  unfold assignedCount
  change rawAssignedCount Q
    (S.chains ++ (Q \ S.vertices).toList.map (fun v => [v])) = _
  rw [rawAssignedCount_append]
  suffices h : rawAssignedCount Q ((Q \ S.vertices).toList.map (fun v => [v])) = 0 by
    simp [h]
  unfold rawAssignedCount
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
  have hvQ := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1
  simp [chainCliqueCount, hvQ]

end CycleClique.Construction.RawPathSystem

end OAI
