import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateLabels
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

namespace Template

theorem initial_slot_role_cases {m k : ℕ} {q : SourceSlot} (hq : q ∈ initial m k) :
    (q.role=.bulk ∧ q.origin < m) ∨
    (q.role=.top ∧ m≤q.origin ∧ q.origin < m+6) ∨
    ∃ j : ℕ, j < k ∧ q.role=.compensation (j+1) ∧
      m+6+4*j≤q.origin ∧ q.origin < m+6+4*j+4 := by
  induction k with
  | zero =>
    rw [InitialCoordinatesTemplate.initial_zero,List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact Or.inl ⟨rfl,by simp⟩
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact Or.inr (Or.inl ⟨rfl,by dsimp; omega,by dsimp; omega⟩)
  | succ k ih =>
    rw [InitialCoordinatesTemplate.initial_succ,List.mem_append] at hq
    rcases hq with hq | hq
    · rcases ih hq with hb | ht | ⟨j,hj,hr,hlo,hhi⟩
      · exact Or.inl hb
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr ⟨j,by omega,hr,hlo,hhi⟩)
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact Or.inr (Or.inr ⟨k,by omega,rfl,by dsimp; omega,by dsimp; omega⟩)
end Template

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem source_role_cases (C : InitialSourceChoice d Bs BD Bz k L E) {q : SourceSlot}
    (hq : q ∈ Template.initial (2*(Conclusion.bulkSize k L/2)) k) :
    (q.role=.bulk ∧ C.sources q.origin=C.bulk) ∨
    (∃ i : Fin 3, q.role=.top ∧ C.sources q.origin=C.auxiliary (.inl i)) ∨
    ∃ j : Fin k, ∃ i : Fin 2, q.role=.compensation (j.val+1) ∧
      C.sources q.origin=C.auxiliary (.inr (j,i)) := by
  rcases Template.initial_slot_role_cases hq with hb | ht | ⟨j,hj,hr,hlo,hhi⟩
  · refine Or.inl ⟨hb.1,?_⟩
    exact initialSourceValue_bulk _ _ _ _ _ hb.2
  · let i : Fin 3 := ⟨(q.origin-2*(Conclusion.bulkSize k L/2))%3,Nat.mod_lt _ (by decide)⟩
    refine Or.inr (Or.inl ⟨i,ht.1,?_⟩)
    have hn : ¬q.origin < 2*(Conclusion.bulkSize k L/2) := by omega
    unfold sources NominalCenterArray.sources initialSourceFamily initialSourceValue
    rw [ite_eq_right hn,ite_eq_left ht.2.2]
    rfl
  · let i : Fin 2 := ⟨(q.origin-(2*(Conclusion.bulkSize k L/2)+6))%2,Nat.mod_lt _ (by decide)⟩
    refine Or.inr (Or.inr ⟨⟨j,hj⟩,i,hr,?_⟩)
    have hn : ¬q.origin < 2*(Conclusion.bulkSize k L/2) := by omega
    have hn' : ¬q.origin < 2*(Conclusion.bulkSize k L/2)+6 := by omega
    have he : (q.origin-(2*(Conclusion.bulkSize k L/2)+6))/4=j := by omega
    have hv : (q.origin-(2*(Conclusion.bulkSize k L/2)+6))/4 < k := by omega
    unfold sources NominalCenterArray.sources initialSourceFamily initialSourceValue
    rw [ite_eq_right hn,ite_eq_right hn',dite_eq_left hv]
    change C.cells.compSource E C.deleted_card ⟨_,hv⟩ i = C.cells.compSource E C.deleted_card ⟨j,hj⟩ i
    congr 1
    exact Fin.ext he

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
