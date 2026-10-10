import OAI.NumberTheory.Ostmann.Construction.AssignmentSplit

namespace OAI

noncomputable section
namespace Ostmann.Construction

def assignmentAppendWeightEquiv (sources : SourceFamily) (T U : List SourceSlot) :
    WeightEquiv (assignmentWeight sources (T++U))
      (fun x : SourceAssignment sources T × SourceAssignment sources U =>
        assignmentWeight sources T x.1*assignmentWeight sources U x.2) := by
  induction T with
  | nil =>
    refine ⟨{ toFun := fun x => ((assignmentNilEquiv sources).symm (),x)
              invFun := fun x => x.2
              left_inv := fun _ => rfl
              right_inv := fun x => by apply Prod.ext; funext i; exact Fin.elim0 i; rfl },?_⟩
    intro x
    change assignmentWeight sources U x=assignmentWeight sources [] ((assignmentNilEquiv sources).symm ()) * assignmentWeight sources U x
    simp only [assignmentWeight_eq_mass,assignmentPrior_nil_mass,one_mul]
  | cons q T ih =>
    exact (assignmentConsWeightEquiv sources q (T++U)).trans
      (((WeightEquiv.refl (sources q.origin).law.mass).prod ih).trans
        ((WeightEquiv.assoc _ _ _).symm.trans
          ((assignmentConsWeightEquiv sources q T).symm.prod (WeightEquiv.refl _))))

def assignmentAppendEquiv (sources : SourceFamily) (T U : List SourceSlot) :=
  (assignmentAppendWeightEquiv sources T U).equiv

theorem assignmentAppend_mass (sources : SourceFamily) (T U : List SourceSlot)
    (x : SourceAssignment sources (T++U)) :
    (assignmentPrior sources (T++U)).mass x =
      (assignmentPrior sources T).mass (assignmentAppendEquiv sources T U x).1 *
      (assignmentPrior sources U).mass (assignmentAppendEquiv sources T U x).2 :=
  (assignmentAppendWeightEquiv sources T U).mass x

end Ostmann.Construction

end

end OAI
