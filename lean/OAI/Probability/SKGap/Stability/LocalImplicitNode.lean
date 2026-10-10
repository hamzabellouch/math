import Mathlib
import OAI.Probability.SKGap.Stability.ImplicitNode

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
variable {n : ℕ}
lemma derivativeMatrix_congr_on_flips (F G : VectorFields n) (x : Spin n)
    (hx : F x=G x) (hf : ∀i,F (flip x i)=G (flip x i)) :
    derivativeMatrix F x=derivativeMatrix G x := by
  ext i k
  simp only [derivativeMatrix,halfDiff_as_flip,hx,hf]
end SKGapCutoff.Primary

namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
open SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

lemma implicit_source_derivative_local (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n)
    (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hwf : ∀i,w (flip x i)=D.sourceOf 1 (fun _=>y) (flip x i)) :
    derivativeMatrix w x=Matrix.diagonal (D.implicitCoefficient x)*derivativeMatrix y x+
      Matrix.diagonal (D.implicitPartial y x)*t.fieldMatrix D.j D.J+D.implicitSourcePrimitive t y x := by
  rw [derivativeMatrix_congr_on_flips w _ x hw hwf,D.sourceOf_derivative]
  simp only [Fintype.sum_unique,implicitCoefficient,implicitPartial,implicitSourcePrimitive,mul_sub]
  have hd : (default : Fin 1)=0 := Subsingleton.elim _ _
  rw [hd]
  abel

lemma implicit_field_derivative_local (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n)
    (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hwf : ∀i,w (flip x i)=D.sourceOf 1 (fun _=>y) (flip x i))
    (hy : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hyf : ∀i,y (flip x i)=D.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i)) :
    derivativeMatrix y x=(D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*derivativeMatrix w x-
      (D.j*siteMean (D.implicitPartial y) x) • t.sourceMatrix D.j D.J+D.implicitFieldPrimitive t w y x := by
  have H:=derivativeMatrix_congr_on_flips y _ x hy hyf
  have HW:=derivativeMatrix_congr_on_flips w _ x hw hwf
  rw [D.fieldOf_derivative,←HW] at H
  simp only [Fintype.sum_unique] at H
  rw [H]
  simp only [implicitCoefficient,implicitPartial,implicitFieldPrimitive,neg_smul,smul_sub,
    sub_mul,smul_mul_assoc,one_mul]
  abel
theorem implicit_error_solved_local (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n)
    (x : Spin n)
    (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hwf : ∀i,w (flip x i)=D.sourceOf 1 (fun _=>y) (flip x i))
    (hy : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hyf : ∀i,y (flip x i)=D.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i))
    (hK : WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
      (1-Matrix.diagonal (D.implicitCoefficient x)*(D.J-(D.j*siteMean D.implicitCoefficient x) • 1))=1) :
    derivativeMatrix w x-D.implicitRetainedSource t y x=
      WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
        (D.implicitSourcePrimitive t y x+Matrix.diagonal (D.implicitCoefficient x)*D.implicitFieldPrimitive t w y x) ∧
    derivativeMatrix y x-D.implicitRetainedField t y x=
      (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*
        (derivativeMatrix w x-D.implicitRetainedSource t y x)+D.implicitFieldPrimitive t w y x := by
  have hsource:=D.implicit_source_derivative_local t w y x hw hwf
  have hfield:=D.implicit_field_derivative_local t w y x hw hwf hy hyf
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
