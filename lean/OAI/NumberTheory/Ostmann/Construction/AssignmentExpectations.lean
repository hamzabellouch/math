import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.AssignmentAppend

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem WeightEquiv.csum_comp {α β : Type*} [Fintype α] [Fintype β]
    {w : α → ℝ} {v : β → ℝ} (e : WeightEquiv w v) (f : β → ℂ) :
    (∑ x,(w x:ℂ)*f (e.equiv x)) = ∑ y,(v y:ℂ)*f y := by
  simp_rw [e.mass]
  exact e.equiv.sum_comp (fun y => (v y:ℂ)*f y)

theorem assignmentSplit_cmean (sources : SourceFamily) (j : ℕ) (T : List SourceSlot)
    (f : SourceAssignment sources (Template.extracted j T) ×
      SourceAssignment sources (Template.remainder j T) → ℂ) :
    (assignmentPrior sources T).cmean (fun x => f (assignmentSplitEquiv sources j T x)) =
      (assignmentPrior sources (Template.extracted j T)).cmean (fun u =>
        (assignmentPrior sources (Template.remainder j T)).cmean (fun h => f (u,h))) := by
  have he := (assignmentSplitWeightEquiv sources j T).csum_comp f
  simpa only [FinitePrior.cmean,Fintype.sum_prod_type,Complex.ofReal_mul,
    assignmentWeight_eq_mass,assignmentSplitEquiv,Finset.mul_sum,mul_assoc] using he

theorem assignmentAppend_cmean (sources : SourceFamily) (T U : List SourceSlot)
    (f : SourceAssignment sources T × SourceAssignment sources U → ℂ) :
    (assignmentPrior sources (T++U)).cmean (fun x => f (assignmentAppendEquiv sources T U x)) =
      (assignmentPrior sources T).cmean (fun x =>
        (assignmentPrior sources U).cmean (fun y => f (x,y))) := by
  have he := (assignmentAppendWeightEquiv sources T U).csum_comp f
  simpa only [FinitePrior.cmean,Fintype.sum_prod_type,Complex.ofReal_mul,
    assignmentWeight_eq_mass,assignmentAppendEquiv,Finset.mul_sum,mul_assoc] using he

end Ostmann.Construction

end

end OAI
