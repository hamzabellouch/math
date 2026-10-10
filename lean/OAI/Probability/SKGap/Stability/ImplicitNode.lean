import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Localization.RecipeError
import OAI.Probability.SKGap.Matrix.ClosedErrorTrace
import OAI.Probability.SKGap.Matrix.ClosedMatrix

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
open SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

def implicitPartial (y : VectorFields n) : VectorFields n := D.partialOf 1 () (fun _=>y)
def implicitCoefficient : VectorFields n := D.auxCoefficient 1 0

def implicitSourcePrimitive (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n) : Interaction n :=
  D.sourceAtoms 1 (fun _=>y) x+Matrix.diagonal (D.implicitPartial y x)*
    (derivativeMatrix (D.H ()) x-t.fieldMatrix D.j D.J)
def implicitFieldPrimitive (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n) : Interaction n :=
  -(D.j*siteMean (D.implicitPartial y) x) •
    (derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J)-
  D.j • (averageError (siteMean (D.implicitPartial y)) (D.predecessor ()) x+
    averageError (siteMean D.implicitCoefficient) w x)

def implicitRetainedSource (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n) : Interaction n :=
  GradedWords.matrixValue D.j (D.implicitCoefficient x) D.J
    (GradedWords.implicitSource D.j (D.implicitCoefficient x) (D.implicitPartial y x) t)
def implicitRetainedField (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n) : Interaction n :=
  GradedWords.matrixValue D.j (D.implicitCoefficient x) D.J
    (GradedWords.implicitField D.j (D.implicitCoefficient x) (D.implicitPartial y x) t)

lemma mean_implicit (F : VectorFields n) (x : Spin n) : Diagram.mean (F x)=siteMean F x := by
  simp [Diagram.mean,siteMean]

lemma implicit_source_derivative (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n)
    (hw : w=D.sourceOf 1 (fun _=>y)) (x : Spin n) :
    derivativeMatrix w x=Matrix.diagonal (D.implicitCoefficient x)*derivativeMatrix y x+
      Matrix.diagonal (D.implicitPartial y x)*t.fieldMatrix D.j D.J+D.implicitSourcePrimitive t y x := by
  rw [hw,D.sourceOf_derivative]
  simp only [Fintype.sum_unique,implicitCoefficient,implicitPartial,implicitSourcePrimitive,mul_sub]
  have hd : (default : Fin 1)=0 := Subsingleton.elim _ _
  rw [hd]
  abel
lemma implicit_field_derivative (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n)
    (hw : w=D.sourceOf 1 (fun _=>y)) (hy : y=D.fieldOf 1 (fun _=>w) (fun _=>y)) (x : Spin n) :
    derivativeMatrix y x=(D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*derivativeMatrix w x-
      (D.j*siteMean (D.implicitPartial y) x) • t.sourceMatrix D.j D.J+D.implicitFieldPrimitive t w y x := by
  have H:=congrArg (fun Q:VectorFields n=>derivativeMatrix Q x) hy
  rw [D.fieldOf_derivative,←hw] at H
  simp only [Fintype.sum_unique] at H
  rw [H]
  simp only [implicitCoefficient,implicitPartial,implicitFieldPrimitive,neg_smul,smul_sub,
    sub_mul,smul_mul_assoc,one_mul]
  abel

theorem implicit_error_solved (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n)
    (hw : w=D.sourceOf 1 (fun _=>y)) (hy : y=D.fieldOf 1 (fun _=>w) (fun _=>y)) (x : Spin n)
    (hK : WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
      (1-Matrix.diagonal (D.implicitCoefficient x)*(D.J-(D.j*siteMean D.implicitCoefficient x) • 1))=1) :
    derivativeMatrix w x-D.implicitRetainedSource t y x=
      WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
        (D.implicitSourcePrimitive t y x+Matrix.diagonal (D.implicitCoefficient x)*D.implicitFieldPrimitive t w y x) ∧
    derivativeMatrix y x-D.implicitRetainedField t y x=
      (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*
        (derivativeMatrix w x-D.implicitRetainedSource t y x)+D.implicitFieldPrimitive t w y x := by
  have hsource:=D.implicit_source_derivative t w y hw x
  have hfield:=D.implicit_field_derivative t w y hw hy x
  have hs : derivativeMatrix w x=Matrix.diagonal (D.implicitCoefficient x)*derivativeMatrix y x+
      (Matrix.diagonal (D.implicitPartial y x)*t.fieldMatrix D.j D.J+D.implicitSourcePrimitive t y x) := by rw [hsource];abel
  have hf : derivativeMatrix y x=(D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*derivativeMatrix w x+
      (-(D.j*siteMean (D.implicitPartial y) x) • t.sourceMatrix D.j D.J+D.implicitFieldPrimitive t w y x) := by
    rw [hfield];simp only [neg_smul];abel
  have H:=implicit_error_elimination _ _ _ _ _ _ _ _ hK hs hf
  constructor
  · rw [H,implicitRetainedSource,GradedWords.matrixValue_implicitSource,mean_implicit]
    simp only [mul_add,mul_sub,neg_smul,mul_neg,mul_smul_comm]
    abel
  · rw [hfield,implicitRetainedField,GradedWords.matrixValue_implicitField,mean_implicit,mean_implicit]
    change _-((D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*D.implicitRetainedSource t y x-
      (D.j*siteMean (D.implicitPartial y) x) • t.sourceMatrix D.j D.J)=_
    rw [mul_sub]
    abel

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
