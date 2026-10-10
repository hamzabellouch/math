import OAI.NumberTheory.Ostmann.Construction.AssignmentExpectations
import OAI.NumberTheory.Ostmann.Construction.AssignmentRestoration

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def restoringAssignmentEquiv (sources : SourceFamily) (j : ℕ) (T : List SourceSlot) :=
  (restoringSplit sources j T).val.equiv

theorem assignedSlots_split_reinsert (sources : SourceFamily) (j : ℕ)
    (T : List SourceSlot) (x : SourceAssignment sources T) :
    assignedSlots sources T x = Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) (restoringAssignmentEquiv sources j T x).1)
      (assignedSlots sources (Template.remainder j T) (restoringAssignmentEquiv sources j T x).2) :=
  (restoringSplit sources j T).property x

theorem assignment_reinsert_cmean (sources : SourceFamily) (j : ℕ) (T : List SourceSlot)
    (F : List SmallSlot → ℂ) :
    (assignmentPrior sources T).cmean (fun x => F (assignedSlots sources T x)) =
      (assignmentPrior sources (Template.extracted j T)).cmean (fun u =>
        (assignmentPrior sources (Template.remainder j T)).cmean (fun h =>
          F (Template.reinsert j T (assignedSlots sources (Template.extracted j T) u)
            (assignedSlots sources (Template.remainder j T) h)))) := by
  have he := (restoringSplit sources j T).val.csum_comp
    (fun x => F (Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) x.1)
      (assignedSlots sources (Template.remainder j T) x.2)))
  simp_rw [← (restoringSplit sources j T).property] at he
  simpa only [FinitePrior.cmean,Fintype.sum_prod_type,Complex.ofReal_mul,
    assignmentWeight_eq_mass,Finset.mul_sum,mul_assoc] using he

namespace FinitePrior

theorem cmean_comm {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (ν : FinitePrior β) (F : α → β → ℂ) :
    μ.cmean (fun x => ν.cmean (F x))=ν.cmean (fun y => μ.cmean (fun x => F x y)) := by
  simp only [cmean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  ring
end FinitePrior

theorem outerPrior_extract (sources : SourceFamily) (j : ℕ) (T : List SourceSlot)
    (giant : PrimeSource) (F : ℕ → ℕ → List SmallSlot → ℂ) :
    (outerPrior sources T giant).cmean (fun x => F x.1 x.2.1 (assignedSlots sources T x.2.2)) =
      giant.law.cmean (fun p =>
        (assignmentPrior sources (Template.extracted j T)).cmean (fun u =>
          giant.law.cmean (fun q =>
            (assignmentPrior sources (Template.remainder j T)).cmean (fun h =>
              F p q (Template.reinsert j T
                (assignedSlots sources (Template.extracted j T) u)
                (assignedSlots sources (Template.remainder j T) h)))))) := by
  unfold outerPrior
  simp_rw [FinitePrior.pair_cmean,assignment_reinsert_cmean sources j T]
  apply congrArg (FinitePrior.cmean giant.law)
  funext p
  exact FinitePrior.cmean_comm _ _ _

end Ostmann.Construction

end

end OAI
