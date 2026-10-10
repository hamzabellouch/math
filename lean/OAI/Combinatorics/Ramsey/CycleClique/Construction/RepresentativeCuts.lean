import OAI.Combinatorics.Ramsey.CycleClique.Construction.Representatives

namespace OAI

/-! Every selected representative is the first vertex of a chain, or
immediately follows a clique vertex. Two cuts in one chain can be ordered. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

def RepCut (Q : Finset V) (l : List V) (x : V) : Prop :=
  ∃ A B : List V, l = A ++ x :: B ∧ ∀ v ∈ A.getLast?, v ∈ Q

theorem representativesFrom_mem_cut {prev x : V} {xs : List V}
    (hx : x ∈ representativesFrom Q prev xs) :
    ∃ A B : List V, prev :: xs = A ++ x :: B ∧
      (∀ v ∈ A.getLast?, v ∈ Q) ∧ A ≠ [] := by
  induction xs generalizing prev with
  | nil => simp [representativesFrom] at hx
  | cons z zs ih =>
    simp only [representativesFrom, List.mem_append] at hx
    by_cases hp : prev ∈ Q
    · simp only [hp, ↓reduceIte, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact ⟨[prev], zs, rfl, by simpa using hp, by simp⟩
      · obtain ⟨A, B, hEq, hA, hne⟩ := ih hx
        refine ⟨prev :: A, B, by simpa using congrArg (List.cons prev) hEq, ?_, by simp⟩
        cases A with
        | nil => exact False.elim (hne rfl)
        | cons a A => simpa using hA
    · simp only [hp, ↓reduceIte, List.not_mem_nil, false_or] at hx
      obtain ⟨A, B, hEq, hA, hne⟩ := ih hx
      refine ⟨prev :: A, B, by simpa using congrArg (List.cons prev) hEq, ?_, by simp⟩
      cases A with
      | nil => exact False.elim (hne rfl)
      | cons a A => simpa using hA

theorem chainRepresentatives_mem_cut {l : List V} {x : V}
    (hx : x ∈ chainRepresentatives Q l) : RepCut Q l x := by
  cases l with
  | nil => simp [chainRepresentatives] at hx
  | cons prev xs =>
    simp only [chainRepresentatives, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨[], xs, rfl, by simp⟩
    · obtain ⟨A, B, he, hA, _⟩ := representativesFrom_mem_cut hx
      exact ⟨A, B, he, hA⟩

private theorem cut_ordered_of_later {l A C D : List V} {x y : V}
    (hnd : l.Nodup) (hx : l = A ++ x :: C ++ y :: D)
    (hy : RepCut Q l y) (hA : ∀ v ∈ A.getLast?, v ∈ Q) :
    ∃ A' B' D' : List V, l = A' ++ (x :: B') ++ y :: D' ∧
      (∀ v ∈ A'.getLast?, v ∈ Q) ∧
      (∀ v ∈ (x :: B').getLast?, v ∈ Q) := by
  obtain ⟨E, F, he, hE⟩ := hy
  have hsplit : l = (A ++ x :: C) ++ y :: D := by simpa [List.append_assoc] using hx
  have hn : ((A ++ x :: C) ++ y :: D).Nodup := hsplit ▸ hnd
  have hny : y ∉ A ++ x :: C := by
    exact fun h => (List.nodup_append'.mp hn).2.2 h (by simp)
  have hnyD : y ∉ D := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
  have heq : (A ++ x :: C) ++ y :: D = E ++ y :: F := hsplit.symm.trans he
  have hpref := (List.append_cons_inj_of_notMem hny hnyD).mp heq
  have hlast : ∀ v ∈ (x :: C).getLast?, v ∈ Q := by
    intro v hv
    apply hE v
    rw [← hpref.1]
    have hs := List.getLast?_eq_some_getLast (show x :: C ≠ [] by simp)
    simpa only [List.getLast?_append, hs, Option.or] using hv
  exact ⟨A, C, D, by simpa [List.append_assoc] using hx, hA, hlast⟩

theorem repCuts_ordered {l : List V} {x y : V} (hnd : l.Nodup) (hne : x ≠ y)
    (hx : RepCut Q l x) (hy : RepCut Q l y) :
    (∃ A B D : List V, l = A ++ (x :: B) ++ y :: D ∧
      (∀ v ∈ A.getLast?, v ∈ Q) ∧ (∀ v ∈ (x :: B).getLast?, v ∈ Q)) ∨
    (∃ A B D : List V, l = A ++ (y :: B) ++ x :: D ∧
      (∀ v ∈ A.getLast?, v ∈ Q) ∧ (∀ v ∈ (y :: B).getLast?, v ∈ Q)) := by
  obtain ⟨A, B, he, hA⟩ := hx
  have hym : y ∈ l := by obtain ⟨C, D, h, _⟩ := hy; simp [h]
  rw [he] at hym
  simp only [List.mem_append, List.mem_cons] at hym
  rcases hym with hym | hye | hym
  · obtain ⟨C, D, hC⟩ := List.append_of_mem hym
    have he' : l = C ++ y :: (D ++ x :: B) := by simp [he, hC, List.append_assoc]
    obtain ⟨E, F, hyEq, hE⟩ := hy
    have hn : (C ++ y :: (D ++ x :: B)).Nodup := he' ▸ hnd
    have hny : y ∉ C := fun h => (List.nodup_append'.mp hn).2.2 h (by simp)
    have hnytail : y ∉ D ++ x :: B := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
    have hpref := (List.append_cons_inj_of_notMem hny hnytail).mp (he'.symm.trans hyEq)
    have hCends : ∀ v ∈ C.getLast?, v ∈ Q := by simpa [hpref.1] using hE
    apply Or.inr
    exact cut_ordered_of_later (A := C) (C := D) (D := B) hnd
      (by simp [he, hC, List.append_assoc])
      ⟨A, B, he, hA⟩ hCends
  · exact False.elim (hne hye.symm)
  · obtain ⟨C, D, hC⟩ := List.append_of_mem hym
    apply Or.inl
    exact cut_ordered_of_later (A := A) (C := C) (D := D) hnd
      (by simp [he, hC, List.append_assoc]) hy hA

end CycleClique.Construction

end OAI
