import Mathlib
import OAI.Probability.SKGap.Localization.ClosedPrediction
import OAI.Probability.SKGap.Matrix.ClosedTrace

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series.GradedWords
open Matrix Diagram InverseDiagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixValue_append (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P Q : GradedWords ι) :
    matrixValue j a J (P++Q)=matrixValue j a J P+matrixValue j a J Q := by
  simp [matrixValue]
lemma matrixValue_scalar (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) :
    matrixValue j a J (scalar c)=c • 1 := by
  simp [matrixValue,scalar,exactWord,matrixFactorProduct]
lemma matrixValue_bump (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) :
    matrixValue j a J (bump P)=matrixValue j a J P := by
  simp [matrixValue,bump,List.map_map,Function.comp_def]
lemma matrixValue_scale (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) :
    matrixValue j a J (scale c P)=c • matrixValue j a J P := by
  induction P with
  | nil => simp [matrixValue,scale]
  | cons t P ih =>
    simp only [scale,List.map_cons,matrixValue,List.sum_cons]
    change (c*t.1) • _+matrixValue j a J (scale c P)=c • (t.1 • _+matrixValue j a J P)
    rw [ih,smul_add,smul_smul]
lemma matrixValue_prepend (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) (l : WordLetter ι) :
    matrixValue j a J (prepend l P)=l.exactEval j a J*matrixValue j a J P := by
  induction P with
  | nil => simp [matrixValue,prepend]
  | cons t P ih =>
    simp only [prepend,List.map_cons,matrixValue,List.sum_cons]
    change t.1 • (l.exactEval j a J*exactWord j a t.2.2 J)+matrixValue j a J (prepend l P)=_
    rw [ih,mul_add,mul_smul_comm]
    rfl
lemma matrixValue_ordinaryWords (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    (matrixValue j a J (ordinaryWords j t).1,matrixValue j a J (ordinaryWords j t).2)=
      (t.sourceMatrix j J,t.fieldMatrix j J) := by
  induction t with
  | leaf c => simp [ordinaryWords,matrixValue_bump,matrixValue_prepend,matrixValue_scalar,
      SourceTree.sourceMatrix_leaf,SourceTree.fieldMatrix_leaf,WordLetter.exactEval]
  | branch p t u ht hu =>
    have hs:=congrArg Prod.fst ht
    have hf:=congrArg Prod.snd ht
    have us:=congrArg Prod.fst hu
    have uf:=congrArg Prod.snd hu
    dsimp only at hs hf us uf
    simp only [ordinaryWords,branch,matrixValue_append,matrixValue_bump,matrixValue_prepend,
      matrixValue_scale,WordLetter.exactEval,hs,hf,us,uf,
      SourceTree.sourceMatrix_branch,SourceTree.fieldMatrix_branch,neg_smul,sub_eq_add_neg]
lemma matrixValue_implicitSource (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    matrixValue j a J (implicitSource j a p t)=WordLetter.inverse.exactEval j a J*
      (Matrix.diagonal p*t.fieldMatrix j J-(j*Diagram.mean p) • (Matrix.diagonal a*t.sourceMatrix j J)) := by
  have hs:=congrArg Prod.fst (matrixValue_ordinaryWords j a J t)
  have hf:=congrArg Prod.snd (matrixValue_ordinaryWords j a J t)
  dsimp only at hs hf
  simp only [implicitSource,matrixValue_prepend,matrixValue_append,matrixValue_scale,
    matrixValue_bump,WordLetter.exactEval,hs,hf,neg_smul,sub_eq_add_neg]
lemma matrixValue_implicitField (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    matrixValue j a J (implicitField j a p t)=
      (J-(j*Diagram.mean a) • 1)*matrixValue j a J (implicitSource j a p t)-
        (j*Diagram.mean p) • t.sourceMatrix j J := by
  have hs:=congrArg Prod.fst (matrixValue_ordinaryWords j a J t)
  dsimp only at hs
  simp only [implicitField,matrixValue_append,matrixValue_bump,matrixValue_prepend,
    matrixValue_scale,WordLetter.exactEval,hs,neg_smul,smul_mul_assoc,one_mul,
    sub_eq_add_neg,add_mul,neg_mul]

end SKGap.Noncrossing.Primary.Tensor.Series.GradedWords

end
end

end OAI
