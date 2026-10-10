import Mathlib
import OAI.Probability.SKGap.Matrix.ClosedMatrix

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series.ClosedTree
open Matrix GradedWords
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ofOrdinary : SourceTree (ι→ℝ)→ClosedTree (ι→ℝ)
  | .leaf c => .leaf c
  | .branch p t u => .branch p (ofOrdinary t) (ofOrdinary u)
omit [DecidableEq ι] in
lemma words_ofOrdinary (j : ℝ) (a : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    (ofOrdinary t).words j a=ordinaryWords j t := by
  induction t with
  | leaf c => rfl
  | branch p t u ht hu => simp only [ofOrdinary,words,ordinaryWords,ht,hu]

def sourceMatrix (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : ClosedTree (ι→ℝ)) :=
  GradedWords.matrixValue j a J (t.words j a).1
def fieldMatrix (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : ClosedTree (ι→ℝ)) :=
  GradedWords.matrixValue j a J (t.words j a).2
lemma sourceMatrix_ofOrdinary (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    (ofOrdinary t).sourceMatrix j a J=t.sourceMatrix j J := by
  rw [sourceMatrix,words_ofOrdinary]
  exact congrArg Prod.fst (matrixValue_ordinaryWords j a J t)
lemma fieldMatrix_ofOrdinary (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    (ofOrdinary t).fieldMatrix j a J=t.fieldMatrix j J := by
  rw [fieldMatrix,words_ofOrdinary]
  exact congrArg Prod.snd (matrixValue_ordinaryWords j a J t)
lemma sourceMatrix_leaf (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) :
    (ClosedTree.leaf c).sourceMatrix j a J=c • 1 := by
  simp [sourceMatrix,words,ordinaryWords,matrixValue_scalar]
lemma fieldMatrix_leaf (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) :
    (ClosedTree.leaf c).fieldMatrix j a J=c • J := by
  simp [fieldMatrix,words,ordinaryWords,matrixValue_bump,matrixValue_prepend,
    matrixValue_scalar,WordLetter.exactEval]
lemma sourceMatrix_branch (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t u : ClosedTree (ι→ℝ)) :
    (ClosedTree.branch p t u).sourceMatrix j a J=
      Matrix.diagonal p*t.fieldMatrix j a J+u.sourceMatrix j a J := by
  simp [sourceMatrix,fieldMatrix,words,GradedWords.branch,matrixValue_append,matrixValue_prepend,
    WordLetter.exactEval]
lemma fieldMatrix_branch (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t u : ClosedTree (ι→ℝ)) :
    (ClosedTree.branch p t u).fieldMatrix j a J=
      J*(Matrix.diagonal p*t.fieldMatrix j a J)-
      (j*Diagram.mean p) • t.sourceMatrix j a J+u.fieldMatrix j a J := by
  simp [sourceMatrix,fieldMatrix,words,GradedWords.branch,matrixValue_append,matrixValue_prepend,
    matrixValue_bump,matrixValue_scale,WordLetter.exactEval,sub_eq_add_neg]
  abel

def branches (xs : List ((ι→ℝ)×ClosedTree (ι→ℝ))) : ClosedTree (ι→ℝ) :=
  xs.foldr (fun t v=>.branch t.1 t.2 v) (.leaf 0)
omit [Fintype ι] [DecidableEq ι] in
lemma branches_leafMass (xs : List ((ι→ℝ)×ClosedTree (ι→ℝ))) : (branches xs).leafMass=0 := by
  induction xs with
  | nil => rfl
  | cons t xs ih => exact ih
lemma branches_source (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ)
    (xs : List ((ι→ℝ)×ClosedTree (ι→ℝ))) :
    (branches xs).sourceMatrix j a J=
      (xs.map (fun t=>Matrix.diagonal t.1*t.2.fieldMatrix j a J)).sum := by
  induction xs with
  | nil => simp [branches,sourceMatrix_leaf]
  | cons t xs ih =>
    simpa only [branches,List.foldr_cons,sourceMatrix_branch,List.map_cons,List.sum_cons] using
      (congrArg (fun Z=>Matrix.diagonal t.1*t.2.fieldMatrix j a J+Z) ih)
lemma branches_field (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ)
    (xs : List ((ι→ℝ)×ClosedTree (ι→ℝ))) :
    (branches xs).fieldMatrix j a J=J*(branches xs).sourceMatrix j a J-
      (xs.map (fun t=>(j*Diagram.mean t.1) • t.2.sourceMatrix j a J)).sum := by
  induction xs with
  | nil => simp [branches,sourceMatrix_leaf,fieldMatrix_leaf]
  | cons t xs ih =>
    change (ClosedTree.branch t.1 t.2 (branches xs)).fieldMatrix j a J=_
    rw [fieldMatrix_branch,ih]
    change _=J*(ClosedTree.branch t.1 t.2 (branches xs)).sourceMatrix j a J-_
    rw [sourceMatrix_branch,mul_add]
    simp only [List.map_cons,List.sum_cons]
    abel

end SKGap.Noncrossing.Primary.Tensor.Series.ClosedTree

end
end

end OAI
