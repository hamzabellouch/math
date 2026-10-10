import Mathlib
import OAI.Probability.SKGap.Localization.GraphPrediction

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

inductive SourceTree (D : Type*) where
  | leaf : ℝ → SourceTree D
  | branch : D → SourceTree D → SourceTree D → SourceTree D

namespace SourceTree
variable {D : Type*}

def leafMass : SourceTree D→ℝ
  | .leaf c => c
  | .branch _ _ b => leafMass b

def words (j : ℝ) : SourceTree (ι→ℝ)→WordPolynomial (ι:=ι)×WordPolynomial (ι:=ι)
  | .leaf c => ([(c,[])],[(c,[.noise])])
  | .branch p a b =>
      (prependWords [.diag p] (words j a).2 ++ (words j b).1,
       (prependWords [.noise,.diag p] (words j a).2 ++
          scale (-(j*Diagram.mean p)) (words j a).1) ++ (words j b).2)

def sourceOperator (j : ℝ) (t : SourceTree (ι→ℝ)) := polynomialOperator j (t.words j).1
def fieldOperator (j : ℝ) (t : SourceTree (ι→ℝ)) := polynomialOperator j (t.words j).2

section
omit [DecidableEq ι]

lemma source_leaf (j c : ℝ) : sourceOperator (ι:=ι) j (.leaf c)=c • LinearMap.id := by
  simp [sourceOperator,words,polynomialOperator,word]
lemma field_leaf (j c : ℝ) : fieldOperator (ι:=ι) j (.leaf c)=c • noise j := by
  simp [fieldOperator,words,polynomialOperator,word,letter]
lemma source_branch (j : ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    sourceOperator j (.branch p a b)=(diagonal p).comp (fieldOperator j a)+sourceOperator j b := by
  simp [sourceOperator,fieldOperator,words,polynomialOperator_append,
    polynomialOperator_prefix,word,letter]
lemma field_branch (j : ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    fieldOperator j (.branch p a b)=
      (noise j).comp ((diagonal p).comp (fieldOperator j a))-
        (j*Diagram.mean p) • sourceOperator j a+fieldOperator j b := by
  simp only [sourceOperator,fieldOperator,words,polynomialOperator_append,
    polynomialOperator_prefix,polynomialOperator_scale,word,letter,LinearMap.comp_id,
    LinearMap.comp_assoc]
  ext v s
  simp [LinearMap.sub_apply,LinearMap.smul_apply,sub_eq_add_neg]

theorem field_vacuum (j : ℝ) (t : SourceTree (ι→ℝ)) :
    fieldOperator j t vacuum=creation (sourceOperator j t vacuum) := by
  induction t with
  | leaf c => simp [field_leaf,source_leaf,noise,vacuum]
  | branch p a b ia ib =>
    rw [field_branch,source_branch]
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
      LinearMap.smul_apply,ia,ib,map_add,noise]
    simp only [annihilation_diagonal_creation,smul_smul]
    abel

theorem field_prediction_zero (j : ℝ) (t : SourceTree (ι→ℝ)) (i : ι) :
    polynomialPrediction j (t.words j).2 i=0 := by
  rw [polynomialPrediction_eq_project]
  change project (fieldOperator j t vacuum) i=0
  rw [field_vacuum,project_creation]; rfl

theorem source_prediction (j : ℝ) (t : SourceTree (ι→ℝ)) (i : ι) :
    polynomialPrediction j (t.words j).1 i=t.leafMass := by
  rw [polynomialPrediction_eq_project]
  change project (sourceOperator j t vacuum) i=t.leafMass
  induction t with
  | leaf c => simp [source_leaf,leafMass,vacuum,project,ket]
  | branch p a b ia ib =>
    rw [source_branch]
    simp only [LinearMap.add_apply,LinearMap.comp_apply,map_add,field_vacuum,
      project_diagonal_creation,zero_add,leafMass]
    exact ib

end

def sourceMatrix (j : ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :=
  matrixPolynomial J (t.words j).1
def fieldMatrix (j : ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :=
  matrixPolynomial J (t.words j).2
lemma sourceMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    sourceMatrix j J (.leaf c)=c • 1 := by simp [sourceMatrix,words,matrixPolynomial,matrixWord]
lemma fieldMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    fieldMatrix j J (.leaf c)=c • J := by
  simp [fieldMatrix,words,matrixPolynomial,matrixWord,matrixLetter]
lemma sourceMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    sourceMatrix j J (.branch p a b)=Matrix.diagonal p*fieldMatrix j J a+sourceMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixWord,matrixLetter]
lemma fieldMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    fieldMatrix j J (.branch p a b)=J*(Matrix.diagonal p*fieldMatrix j J a)-
      (j*Diagram.mean p) • sourceMatrix j J a+fieldMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixPolynomial_scale,matrixWord,matrixLetter,mul_assoc,sub_eq_add_neg,add_assoc]
end SourceTree
end SKGap.Noncrossing.Primary

end
end

end OAI
