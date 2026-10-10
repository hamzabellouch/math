import OAI.NumberTheory.Ostmann.Construction.PrimeSources

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def assignmentConsEquiv (sources : SourceFamily) (q : SourceSlot) (T : List SourceSlot) :
    SourceAssignment sources (q::T) ≃ (sources q.origin).Sample×SourceAssignment sources T where
  toFun x := (x 0,fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by rfl

theorem assignmentPrior_cons_mass (sources : SourceFamily) (q : SourceSlot)
    (T : List SourceSlot) (x : SourceAssignment sources (q::T)) :
    (assignmentPrior sources (q::T)).mass x =
      (sources q.origin).law.mass (assignmentConsEquiv sources q T x).1 *
        (assignmentPrior sources T).mass (assignmentConsEquiv sources q T x).2 := by
  simp only [assignmentPrior,dependentProductPrior]
  exact Fin.prod_univ_succ (fun i : Fin (T.length+1) =>
    (sources (q::T)[i].origin).law.mass (x i))

def assignmentNilEquiv (sources : SourceFamily) : SourceAssignment sources [] ≃ Unit where
  toFun _ := ()
  invFun _ := fun i => Fin.elim0 i
  left_inv x := by funext i; exact Fin.elim0 i
  right_inv x := by cases x; rfl

@[simp] theorem assignmentPrior_nil_mass (sources : SourceFamily)
    (x : SourceAssignment sources []) : (assignmentPrior sources []).mass x=1 := by
  simp [assignmentPrior,dependentProductPrior]

end Ostmann.Construction

end

end OAI
