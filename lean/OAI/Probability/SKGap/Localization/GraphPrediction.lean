import Mathlib
import OAI.Probability.SKGap.Matrix.PrimaryMatrix

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram
variable {ι : Type*} [Fintype ι]

lemma annihilation_diagonal_creation (a : D (ι:=ι)) (v : Space (ι:=ι)) :
    annihilation (diagonal a (creation v))=Diagram.mean a • v := by
  have he : annihilation.comp ((diagonal a).comp creation)=
      Diagram.mean a • (LinearMap.id : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [creation,diagonal,annihilation,ket,mul_comm]
  exact LinearMap.congr_fun he v

omit [Fintype ι] in
lemma project_diagonal_creation (a : D (ι:=ι)) (v : Space (ι:=ι)) :
    project (diagonal a (creation v))=0 := by
  have he : project.comp ((diagonal a).comp creation)=
      (0 : Space (ι:=ι)→ₗ[ℝ] D (ι:=ι)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [creation,diagonal,project,ket]
  exact LinearMap.congr_fun he v

omit [Fintype ι] in
lemma project_creation (v : Space (ι:=ι)) : project (creation v)=0 := by
  have he : project.comp creation=(0 : Space (ι:=ι)→ₗ[ℝ] D (ι:=ι)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [creation,project,ket]
  exact LinearMap.congr_fun he v

namespace Graph
variable {α : Type*} [Fintype α]

def sumWords (P : α→WordPolynomial (ι:=ι)) : WordPolynomial (ι:=ι) :=
  (Finset.univ.toList.map P).flatten

lemma polynomialOperator_sumWords (j : ℝ) (P : α→WordPolynomial (ι:=ι)) :
    polynomialOperator j (sumWords P)=∑ a,polynomialOperator j (P a) := by
  simp [sumWords,polynomialOperator,List.map_flatten,List.map_map,Function.comp_def]

lemma matrixPolynomial_sumWords [DecidableEq ι] (J : Matrix ι ι ℝ) (P : α→WordPolynomial (ι:=ι)) :
    matrixPolynomial J (sumWords P)=∑ a,matrixPolynomial J (P a) := by
  simp [sumWords,matrixPolynomial,List.map_flatten,List.map_map,Function.comp_def]

abbrev Partials := α→α→D (ι:=ι)

def sourceWords (p : Partials (ι:=ι) (α:=α)) (H : α→WordPolynomial (ι:=ι))
    (a : α) : WordPolynomial (ι:=ι) :=
  sumWords (fun d => prependWords [.diag (p a d)] (H d))
def fieldWords (j : ℝ) (p : Partials (ι:=ι) (α:=α))
    (S T : α→WordPolynomial (ι:=ι)) (a : α) : WordPolynomial (ι:=ι) :=
  prependWords [.noise] (S a) ++
    sumWords (fun d => scale (-(j*Diagram.mean (p a d))) (T d))

def coefficients (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) :
    ℕ→(α→WordPolynomial (ι:=ι))×(α→WordPolynomial (ι:=ι))
  | 0 => (fun a => [(r a,[])],fun _ => [])
  | 1 =>
      let H := fun a => prependWords [.noise] [(r a,[])]
      (sourceWords p H,H)
  | m+2 =>
      let H := fieldWords j p (coefficients j p r (m+1)).1 (coefficients j p r m).1
      (sourceWords p H,H)

def sourceOp (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (m : ℕ) (a : α) :=
  polynomialOperator j ((coefficients j p r m).1 a)
def fieldOp (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (m : ℕ) (a : α) :=
  polynomialOperator j ((coefficients j p r m).2 a)

lemma sourceOp_zero (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (a : α) :
    sourceOp j p r 0 a=r a • LinearMap.id := by
  simp [sourceOp,coefficients,polynomialOperator,word]
lemma fieldOp_zero (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (a : α) :
    fieldOp j p r 0 a=0 := by simp [fieldOp,coefficients,polynomialOperator]
lemma fieldOp_one (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (a : α) :
    fieldOp j p r 1 a=(noise j).comp (sourceOp j p r 0 a) := by
  change polynomialOperator j (prependWords [.noise] [(r a,[])])=_
  rw [polynomialOperator_prefix,sourceOp_zero]
  simp [polynomialOperator,word,letter]
lemma sourceOp_succ (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (m : ℕ) (a : α) :
    sourceOp j p r (m+1) a=∑ d,(diagonal (p a d)).comp (fieldOp j p r (m+1) d) := by
  cases m <;> simp [sourceOp,fieldOp,coefficients,sourceWords,polynomialOperator_sumWords,
    polynomialOperator_prefix,word,letter]
lemma fieldOp_add_two (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (m : ℕ) (a : α) :
    fieldOp j p r (m+2) a=(noise j).comp (sourceOp j p r (m+1) a)-
      ∑ d,(j*Diagram.mean (p a d)) • sourceOp j p r m d := by
  simp only [fieldOp,sourceOp,coefficients,fieldWords,polynomialOperator_append,
    polynomialOperator_sumWords,polynomialOperator_prefix,polynomialOperator_scale,
    word,letter,LinearMap.comp_id]
  ext v s
  simp [LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.sum_neg_distrib,sub_eq_add_neg]

theorem field_vacuum (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ) (m : ℕ) (a : α) :
    fieldOp j p r (m+1) a vacuum=creation (sourceOp j p r m a vacuum) := by
  induction m generalizing a with
  | zero => simp [fieldOp_one,sourceOp_zero,noise,vacuum]
  | succ m ih =>
    rw [show m+1+1=m+2 by omega,fieldOp_add_two]
    simp only [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,noise,LinearMap.add_apply]
    have hs : annihilation (sourceOp j p r (m+1) a vacuum)=
        ∑ d,Diagram.mean (p a d) • sourceOp j p r m d vacuum := by
      rw [sourceOp_succ]
      simp only [LinearMap.sum_apply,LinearMap.comp_apply,map_sum,ih,
        annihilation_diagonal_creation]
    rw [hs]
    simp only [Finset.smul_sum,smul_smul]
    exact add_sub_cancel_right _ _

theorem field_prediction_zero (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ)
    (m : ℕ) (a : α) (i : ι) :
    polynomialPrediction j ((coefficients j p r m).2 a) i=0 := by
  rw [polynomialPrediction_eq_project]
  change project (fieldOp j p r m a vacuum) i=0
  cases m with
  | zero => simp [fieldOp_zero]
  | succ m => rw [field_vacuum,project_creation]; rfl

theorem source_prediction_zero (j : ℝ) (p : Partials (ι:=ι) (α:=α)) (r : α→ℝ)
    (m : ℕ) (a : α) (i : ι) :
    polynomialPrediction j ((coefficients j p r (m+1)).1 a) i=0 := by
  rw [polynomialPrediction_eq_project]
  change project (sourceOp j p r (m+1) a vacuum) i=0
  rw [sourceOp_succ]
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,map_sum,field_vacuum,
    project_diagonal_creation,Finset.sum_const_zero,Pi.zero_apply]

end Graph
end SKGap.Noncrossing.Primary

end
end

end OAI
