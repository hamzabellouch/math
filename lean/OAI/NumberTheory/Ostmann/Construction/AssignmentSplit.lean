import OAI.NumberTheory.Ostmann.Construction.AssignmentCons
import OAI.NumberTheory.Ostmann.Construction.TemplateReinsert
import OAI.NumberTheory.Ostmann.Construction.WeightEquiv

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def assignmentWeight (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) : ℝ := ∏ i,(sources T[i].origin).law.mass (x i)

theorem assignmentWeight_eq_mass (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) :
    assignmentWeight sources T x=(assignmentPrior sources T).mass x := rfl

def assignmentConsWeightEquiv (sources : SourceFamily) (q : SourceSlot) (T : List SourceSlot) :
    WeightEquiv (assignmentWeight sources (q::T))
      (fun x : (sources q.origin).Sample×SourceAssignment sources T =>
        (sources q.origin).law.mass x.1*assignmentWeight sources T x.2) :=
  ⟨assignmentConsEquiv sources q T,assignmentPrior_cons_mass sources q T⟩

def assignmentSplitWeightEquiv (sources : SourceFamily) (j : ℕ) (T : List SourceSlot) :
    WeightEquiv (assignmentWeight sources T)
      (fun x : SourceAssignment sources (Template.extracted j T) ×
        SourceAssignment sources (Template.remainder j T) =>
        assignmentWeight sources (Template.extracted j T) x.1*
          assignmentWeight sources (Template.remainder j T) x.2) := by
  induction T with
  | nil =>
    refine ⟨{ toFun := fun x => (x,x)
              invFun := fun x => x.1
              left_inv := fun _ => rfl
              right_inv := fun x => by apply Prod.ext; rfl; funext i; exact Fin.elim0 i },?_⟩
    intro x
    change assignmentWeight sources [] x=assignmentWeight sources [] x*assignmentWeight sources [] x
    simp only [assignmentWeight_eq_mass,assignmentPrior_nil_mass,one_mul]
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · have he : Template.extracted j (q::T)=q::Template.extracted j T := by
        simp [Template.extracted,hq]
      have hr : Template.remainder j (q::T)=Template.remainder j T := by
        simp [Template.remainder,hq]
      rw [he,hr]
      exact (assignmentConsWeightEquiv sources q T).trans
        (((WeightEquiv.refl (sources q.origin).law.mass).prod ih).trans
          ((WeightEquiv.assoc _ _ _).symm.trans
            ((assignmentConsWeightEquiv sources q (Template.extracted j T)).symm.prod
              (WeightEquiv.refl _))))
    · have he : Template.extracted j (q::T)=Template.extracted j T := by
        simp [Template.extracted,hq]
      have hr : Template.remainder j (q::T)=q::Template.remainder j T := by
        simp [Template.remainder,hq]
      rw [he,hr]
      exact (assignmentConsWeightEquiv sources q T).trans
        (((WeightEquiv.refl (sources q.origin).law.mass).prod ih).trans
          ((WeightEquiv.swap _ _ _).trans
            ((WeightEquiv.refl _).prod
              (assignmentConsWeightEquiv sources q (Template.remainder j T)).symm)))

def assignmentSplitEquiv (sources : SourceFamily) (j : ℕ) (T : List SourceSlot) :=
  (assignmentSplitWeightEquiv sources j T).equiv

theorem assignmentSplit_mass (sources : SourceFamily) (j : ℕ) (T : List SourceSlot)
    (x : SourceAssignment sources T) :
    (assignmentPrior sources T).mass x =
      (assignmentPrior sources (Template.extracted j T)).mass
        (assignmentSplitEquiv sources j T x).1 *
      (assignmentPrior sources (Template.remainder j T)).mass
        (assignmentSplitEquiv sources j T x).2 :=
  (assignmentSplitWeightEquiv sources j T).mass x

end Ostmann.Construction

end

end OAI
