import Mathlib
import OAI.Algebra.GroupRing.ConePicture
import OAI.Algebra.GroupRing.GraphConePresentation

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConePicture
open PortSubdivision GraphPresentation
open scoped Classical
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ)
  (letters : D→FreeGroup S)
def wordLabel : Dart Γ R→FreeGroup (GraphConePresentation.Generator (S:=S) Γ R)
  | .inl d => GraphConePresentation.old Γ R (letters d)
  | .inr (v,b) => if b then FreeGroup.of (Sum.inr v) else (FreeGroup.of (Sum.inr v))⁻¹
lemma wordLabel_reverse (hl : ∀d,letters (Γ.reverse d)=(letters d)⁻¹) (d : Dart Γ R) :
    wordLabel Γ R letters ((graph Γ R).reverse d)=(wordLabel Γ R letters d)⁻¹ := by
  rcases d with d|⟨v,b⟩
  · exact (congrArg (GraphConePresentation.old Γ R) (hl d)).trans (map_inv _ _)
  · cases b <;> simp [wordLabel,graph,reverse]
def rootPath (v : V) : Path (graph Γ R) (R.base v) v :=
  if h : v=R.base v then (Path.nil (Γ:=graph Γ R) (R.base v)).cast rfl h.symm
  else (Path.single (Γ:=graph Γ R) (Sum.inr (⟨v,h⟩,true))).cast
    (show (graph Γ R).origin (Sum.inr (⟨v,h⟩,true))=R.base v from rfl)
    (show (graph Γ R).origin ((graph Γ R).reverse (Sum.inr (⟨v,h⟩,true)))=v from rfl)
lemma rootPath_eval (v : V) :
    (rootPath Γ R v).eval (wordLabel Γ R letters)=GraphConePresentation.radial Γ R v := by
  by_cases hv : v=R.base v
  · simp only [rootPath,dite_eq_left hv,Path.eval_cast,Path.eval_nil,GraphConePresentation.radial]
  · simp only [rootPath,dite_eq_right hv,Path.eval_cast,Path.eval_single,wordLabel,ite_true,
      GraphConePresentation.radial]
/-- The actual triangular closed boundary, with a root radial omitted exactly
when it is collapsed in the finite CW model. No directed-edge duplication. -/
def trianglePath (d : D) : Path (graph Γ R) (R.base (Γ.origin d)) (R.base (Γ.origin d)) :=
  ((rootPath Γ R (Γ.origin d)).append
    (((Path.single (Γ:=graph Γ R) (Sum.inl d)).cast
      (show (graph Γ R).origin (Sum.inl d)=Γ.origin d from rfl)
      (show (graph Γ R).origin ((graph Γ R).reverse (Sum.inl d))=Γ.origin (Γ.reverse d) from rfl)).append ((rootPath Γ R (Γ.origin (Γ.reverse d))).reverse))).cast
      rfl (R.same d).symm
lemma trianglePath_eval (hl : ∀d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    (trianglePath Γ R d).eval (wordLabel Γ R letters)=GraphConePresentation.triangle Γ letters R d := by
  rw [trianglePath,Path.eval_cast,Path.eval_append (Γ:=graph Γ R),
    Path.eval_append (Γ:=graph Γ R),Path.eval_cast,Path.eval_single (Γ:=graph Γ R),
    Path.eval_reverse _ (wordLabel_reverse Γ R letters hl),rootPath_eval,rootPath_eval]
  exact (mul_assoc _ _ _).symm
end TorsionFreeZeroDivisors.ConePicture
namespace TorsionFreeZeroDivisors.SampleGraph.ConeSpherePicture
open scoped Classical
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
theorem reduces_to_empty
    (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep))
    (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
    {O : Type} [Fintype O]
    (a : SphericalPicture.Data (O:=O) (ConePicture.graph (graph rep r) (ConcreteGroup.routes rep r))
      (ConePicture.labels (graph rep r) (ConcreteGroup.routes rep r) (label rep))
      (ConePicture.inverse (graph rep r) (ConcreteGroup.routes rep r) Types.inverse)) :
    SphericalPicture.ReducesToEmpty _ _ _ a := by
  apply ConePicture.reduces_to_empty a Types.inverse_inverse (fun d=>label_reverse rep r d)
  intro P _ _ b hb
  exact SpherePicture.excluded b hb hL hd hsample havoid
end TorsionFreeZeroDivisors.SampleGraph.ConeSpherePicture

end

end OAI
