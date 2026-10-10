import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeOutside
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPermutation

namespace OAI

/-! An interior representative has a successor that is not a representative. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem representative_successor (U : RawPathSystem G Q) {x : V}
    (hx : x ∈ U.representatives) (hxQ : x ∉ Q) :
    ∃ l ∈ U.chains, ∃ A : List V, ∃ y : V, ∃ B : List V,
      l = A ++ x :: y :: B ∧ y ∉ U.representatives := by
  obtain ⟨r, hr, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, heqr⟩ := List.mem_map.mp hr
  subst r
  obtain ⟨A, B, he, _⟩ := chainRepresentatives_mem_cut hx
  have hBne : B ≠ [] := by
    intro hB
    have hxLast : x ∈ l.getLast? := by simp [he, hB]
    exact hxQ ((U.endpoints l hl).2 x hxLast)
  cases B with
  | nil => exact False.elim (hBne rfl)
  | cons y B =>
    refine ⟨l, hl, A, y, B, he, ?_⟩
    intro hy
    obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
    obtain ⟨m, hm, heqr⟩ := List.mem_map.mp hr
    subst r
    have hym : y ∈ m := (chainRepresentatives_sublist m).subset hy
    by_cases hlm : l = m
    · subst m
      obtain ⟨C, D, hc, hC⟩ := chainRepresentatives_mem_cut hy
      have he' : l = (A ++ [x]) ++ y :: B := by simpa [List.append_assoc] using he
      have hn : ((A ++ [x]) ++ y :: B).Nodup := he' ▸ (U.paths l hl).1
      have hny : y ∉ A ++ [x] := fun h => (List.nodup_append'.mp hn).2.2 h (by simp)
      have hnyB : y ∉ B := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
      have hpref := (List.append_cons_inj_of_notMem hny hnyB).mp (he'.symm.trans hc)
      apply hxQ
      apply hC x
      rw [← hpref.1]
      simp
    · have hyl : y ∈ l := by simp [he]
      exact List.disjoint_left.mp (U.disjoint_of_mem hl hm hlm) hyl hym

theorem exists_two_outside_completed_representatives (S : ExpandedPathSystem G Q)
    (he : 2 ≤ S.assignedCount) :
    ∃ x ∈ S.toRaw.completeClique.representatives,
      ∃ y ∈ S.toRaw.completeClique.representatives, x ≠ y ∧ x ∉ Q ∧ y ∉ Q := by
  let L := S.toRaw.completeClique.representatives
  let O := L.filter (fun v => decide (v ∉ Q))
  have hO : O.Nodup := S.toRaw.completeClique.representatives_nodup.filter _
  have hcard : 2 ≤ O.toFinset.card := by
    rw [List.toFinset_card_of_nodup hO]
    change 2 ≤ chainOutsideCount Q S.toRaw.completeClique.representatives
    rw [completed_representatives_outside_count]
    exact he
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  have hx' : x ∈ L ∧ x ∉ Q := by simpa [O] using hx
  have hy' : y ∈ L ∧ y ∉ Q := by simpa [O] using hy
  exact ⟨x, hx'.1, y, hy'.1, hxy, hx'.2, hy'.2⟩

end CycleClique.Construction.RawPathSystem

end OAI
