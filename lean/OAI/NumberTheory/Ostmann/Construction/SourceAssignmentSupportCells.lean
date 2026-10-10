import OAI.NumberTheory.Ostmann.Construction.RemainingRows
import OAI.NumberTheory.Ostmann.Construction.SelectedSourceSupport
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem assignment_nonbulk_log_support (C : InitialSourceChoice d Bs BD Bz k L E)
    (T : List SourceSlot)
    (hT : ∀q∈T,q∈Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (x : SourceAssignment C.sources T) (hx : (assignmentPrior C.sources T).mass x≠0) :
    ∀z∈assignedSlots C.sources T x,z.role≠.bulk →
      |Real.log (z.value:ℝ)-C.cells.center (Conclusion.bulkSize k L/2) z.origin|≤1 := by
  intro z hz hrole
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  have hi := Template.initial_nonbulk_origin_bounds
    (hT T[i] (List.getElem_mem i.isLt)) hrole
  exact (C.source_log_support T[i].origin hi.1 hi.2 (x i)
    (assignmentPrior_component_mass_ne_zero C.sources T x hx i)).le

theorem current_nonbulk_log_support (C : InitialSourceChoice d Bs BD Bz k L E)
    (l : ℕ)
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass x≠0) :
    ∀z∈assignedSlots C.sources (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) x,
      z.role≠.bulk → |Real.log (z.value:ℝ)-C.cells.center (Conclusion.bulkSize k L/2) z.origin|≤1 :=
  C.assignment_nonbulk_log_support _ (fun _ hq => Template.mem_current_mem_seed hq) x hx

theorem extracted_log_support (C : InitialSourceChoice d Bs BD Bz k L E)
    (j l : ℕ)
    (x : SourceAssignment C.sources (Template.extracted j
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)))
    (hx : (assignmentPrior C.sources (Template.extracted j
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))).mass x≠0) :
    ∀z∈assignedSlots C.sources (Template.extracted j
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)) x,
      |Real.log (z.value:ℝ)-C.cells.center (Conclusion.bulkSize k L/2) z.origin|≤1 := by
  intro z hz
  apply C.assignment_nonbulk_log_support _
    (fun _ hq => Template.mem_extracted_current_mem_seed hq) x hx z hz
  have hr := assignedSlots_extracted_roles C.sources _ j x z hz
  rw [hr]
  exact SlotRole.noConfusion

theorem remaining_log_support (C : InitialSourceChoice d Bs BD Bz k L E)
    (j l : ℕ)
    (y : RemainingSample C.sources (Template.remainder j
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)) C.giant)
    (hy : (remainingPrior C.sources (Template.remainder j
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)) C.giant).mass y≠0) :
    |Real.log (y.1.val:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
    ∀z∈assignedSlots C.sources (Template.remainder j
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)) y.2,
      z.role≠.bulk → |Real.log (z.value:ℝ)-C.cells.center (Conclusion.bulkSize k L/2) z.origin|≤1 := by
  change C.giant.law.mass y.1 * (assignmentPrior C.sources _).mass y.2≠0 at hy
  obtain ⟨hq,hx⟩ := mul_ne_zero_iff.mp hy
  exact ⟨(C.giant_log_support y.1 hq).le,C.assignment_nonbulk_log_support _
    (fun _ hz => Template.mem_remainder_current_mem_seed hz) y.2 hx⟩

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
