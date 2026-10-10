import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateLabels
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation
open Construction

theorem initial_source_metadata {m k : ℕ} {q : SourceSlot}
    (hq : q∈Template.initial m k) :
    (q.role=.bulk ∧ q.origin < m) ∨
    (q.role=.top ∧ m ≤ q.origin ∧ q.origin < m+6) ∨
    ∃ j : Fin k, q.role=.compensation (j.val+1) ∧
      m+6+4*j.val≤q.origin ∧ q.origin < m+6+4*j.val+4 := by
  induction k with
  | zero =>
    rw [InitialCoordinatesTemplate.initial_zero] at hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact Or.inl ⟨rfl,by simp⟩
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact Or.inr (Or.inl ⟨rfl,by dsimp only; omega,by have hi:=i.isLt; dsimp only; omega⟩)
  | succ k ih =>
    rw [InitialCoordinatesTemplate.initial_succ] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases ih hq with h | h | ⟨j,hrole,hlo,hhi⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨j.castSucc,hrole,hlo,hhi⟩)
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact Or.inr (Or.inr ⟨⟨k,by omega⟩,rfl,by dsimp only; omega,
        by have hi:=i.isLt; dsimp only; omega⟩)

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem source_of_bulk (C : InitialSourceChoice d Bs BD Bz k L E) {q : SourceSlot}
    (h : q.origin<2*(Conclusion.bulkSize k L/2)) : C.sources q.origin=C.bulk :=
  initialSourceValue_bulk _ _ _ _ _ h

theorem source_of_top (C : InitialSourceChoice d Bs BD Bz k L E) {q : SourceSlot}
    (hlo : 2*(Conclusion.bulkSize k L/2)≤q.origin)
    (hhi : q.origin<2*(Conclusion.bulkSize k L/2)+6) :
    ∃ i : Fin 3,C.sources q.origin=C.auxiliary (.inl i) := by
  refine ⟨⟨(q.origin-2*(Conclusion.bulkSize k L/2))%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  change initialSourceValue _ _ _ _ _ _=_
  simp only [initialSourceValue,show ¬q.origin<2*(Conclusion.bulkSize k L/2) by omega,
    ite_false,hhi,ite_true]
  rfl

theorem source_of_comp (C : InitialSourceChoice d Bs BD Bz k L E) {q : SourceSlot}
    (j : Fin k) (hlo : 2*(Conclusion.bulkSize k L/2)+6+4*j.val≤q.origin)
    (hhi : q.origin<2*(Conclusion.bulkSize k L/2)+6+4*j.val+4) :
    ∃ i : Fin 2,C.sources q.origin=C.auxiliary (.inr (j,i)) := by
  refine ⟨⟨(q.origin-(2*(Conclusion.bulkSize k L/2)+6))%2,Nat.mod_lt _ (by decide)⟩,?_⟩
  have he : (q.origin-(2*(Conclusion.bulkSize k L/2)+6))/4=j.val := by omega
  change initialSourceValue _ _ _ _ _ _=_
  simp only [initialSourceValue,show ¬q.origin<2*(Conclusion.bulkSize k L/2) by omega,
    ite_false,show ¬q.origin<2*(Conclusion.bulkSize k L/2)+6 by omega,he,j.isLt,↓reduceDIte]
  rfl

theorem source_disjoint_of_comp (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    {q r : SourceSlot}
    (hq : q∈Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (hr : r∈Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    {j : ℕ} (hrole : q.role=.compensation j) (hne : r.role≠q.role) :
    (C.sources q.origin).DisjointMass (C.sources r.origin) := by
  rcases initial_source_metadata hq with h | h | ⟨a,ha,hlo,hhi⟩
  · simp [hrole] at h
  · simp [hrole] at h
  obtain ⟨i,hi⟩ := source_of_comp C a hlo hhi
  rw [hi]
  rcases initial_source_metadata hr with h | h | ⟨b,hb,hrlo,hrhi⟩
  · rw [source_of_bulk C h.2]
    exact (hsep.bulk_aux _).symm
  · obtain ⟨r,he⟩ := source_of_top C h.2.1 h.2.2
    rw [he]
    exact (hsep.top_comp r a i).symm
  · obtain ⟨r,he⟩ := source_of_comp C b hrlo hrhi
    rw [he]
    apply hsep.comp_comp a b _ i r
    intro hab
    apply hne
    subst b
    exact hb.trans ha.symm

theorem sourceMass_ne_of_disjoint {sources : SourceFamily} {q r : SmallSlot}
    (h : (sources q.origin).DisjointMass (sources r.origin))
    (hq : sourceMass sources q≠0) (hr : sourceMass sources r≠0) : q.value≠r.value := by
  unfold sourceMass at hq hr
  split_ifs at hq with hqm
  · split_ifs at hr with hrm
    · exact h ⟨q.value,hqm⟩ ⟨r.value,hrm⟩ hq hr
    · exact (hr rfl).elim
  · exact (hq rfl).elim

end Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation

end

end OAI
