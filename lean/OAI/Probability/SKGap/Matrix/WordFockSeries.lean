import Mathlib
import OAI.Probability.SKGap.Localization.FockSeries

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]

def wordOperator (j : ℝ) (a : ι→ℝ) : List (WordLetter ι)→Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι)
  | [] => LinearMap.id
  | .diag d::F => (act (diagonal d)).comp (wordOperator j a F)
  | .noise::F => (act (noise j)).comp (wordOperator j a F)
  | .inverse::F => (inverse j a).comp (wordOperator j a F)

def wordSeq (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) : Seq (ι:=ι) :=
  wordOperator j a F (ofVector vacuum)

omit [Fintype ι] in
lemma act_comp (A B : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) :
    act (A.comp B)=(act A).comp (act B) := rfl
omit [Fintype ι] in
lemma act_ofVector (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) (v : Space (ι:=ι)) :
    act A (ofVector v)=ofVector (A v) := by
  funext n
  simp only [act_apply,ofVector]
  split_ifs <;> simp
lemma wordOperator_append (j : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι)) :
    wordOperator j a (P++Q)=(wordOperator j a P).comp (wordOperator j a Q) := by
  induction P with
  | nil => simp [wordOperator]
  | cons l P ih => cases l <;> simp [wordOperator,ih,LinearMap.comp_assoc]
lemma wordOperator_lift (j : ℝ) (a : ι→ℝ) (P : List (Letter (ι→ℝ))) :
    wordOperator j a (liftWord P)=act (word j P) := by
  induction P with
  | nil => rfl
  | cons l P ih => cases l <;> simp only [liftWord_cons,Letter.toWord,wordOperator,word,letter,ih,act_comp]
lemma wordSeq_lift (j : ℝ) (a : ι→ℝ) (P : List (Letter (ι→ℝ))) :
    wordSeq j a (liftWord P)=ofVector (word j P vacuum) := by
  rw [wordSeq,wordOperator_lift,act_ofVector]
lemma wordSeq_oneInverse (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) :
    wordSeq j a (liftWord P++(.inverse::liftWord Q)) n=
      word j P (kernel j a n (word j Q vacuum)) := by
  simp only [wordSeq,wordOperator_append,wordOperator,wordOperator_lift,
    LinearMap.comp_apply,act_ofVector,act_apply,inverse_ofVector]
lemma project_kernel_sandwich (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    project (word j P (kernel j a n (word j Q vacuum))) i=inverseCoefficient j a P Q n i := by
  simp only [kernel,LinearMap.sum_apply,map_sum,Finset.sum_apply,inverseCoefficient]
  apply Finset.sum_congr rfl
  intro bs _
  rw [←Tensor.project_word,word_append,word_append]
  rfl

theorem wordSeq_project_coeff (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι))
    (hF : inverseCount F≤1) (n : ℕ) (i : ι) :
    project (wordSeq j a F n) i=(wordPredictionPolynomial j a F i).coeff n := by
  have h:=congrArg (PowerSeries.coeff n)
    (literalSeries_eq_wordPredictionPolynomial j a F hF i)
  rw [Polynomial.coeff_coe] at h
  rw [←h]
  rcases one_inverse_cases F hF with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
  · rw [wordSeq_lift,literalSeries_lift]
    simp only [ofVector,PowerSeries.coeff_C]
    split_ifs <;> simp_all [Tensor.project_word]
  · rw [wordSeq_oneInverse,project_kernel_sandwich,literalSeries_oneInverse,coeff_inverseSeries]

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]

def shifts : ℕ→Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι)
  | 0 => LinearMap.id
  | n+1 => shift.comp (shifts n)

def letterOperator (j : ℝ) (a : ι→ℝ) : WordLetter ι→Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι)
  | .diag d => act (diagonal d)
  | .noise => act (noise j)
  | .inverse => inverse j a
lemma letter_shift (j : ℝ) (a : ι→ℝ) (l : WordLetter ι) (v : Seq (ι:=ι)) :
    letterOperator j a l (shift v)=shift (letterOperator j a l v) := by
  cases l with
  | diag d => exact act_shift _ _
  | noise => exact act_shift _ _
  | inverse => exact inverse_shift _ _ _
lemma letter_shifts (j : ℝ) (a : ι→ℝ) (l : WordLetter ι) (n : ℕ) (v : Seq (ι:=ι)) :
    letterOperator j a l (shifts n v)=shifts n (letterOperator j a l v) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [shifts,LinearMap.comp_apply,letter_shift] using congrArg shift ih
lemma wordSeq_cons (j : ℝ) (a : ι→ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    wordSeq j a (l::F)=letterOperator j a l (wordSeq j a F) := by cases l <;> rfl

abbrev GradedWords (ι : Type*) := List (ℝ×ℕ×List (WordLetter ι))
namespace GradedWords

def scalar (c : ℝ) : GradedWords ι := [(c,0,[])]
def scale (c : ℝ) (P : GradedWords ι) : GradedWords ι := P.map (fun t=>(c*t.1,t.2))
def bump (P : GradedWords ι) : GradedWords ι := P.map (fun t=>(t.1,t.2.1+1,t.2.2))
def prepend (l : WordLetter ι) (P : GradedWords ι) : GradedWords ι := P.map (fun t=>(t.1,t.2.1,l::t.2.2))
def seq (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) : Seq (ι:=ι) :=
  (P.map (fun t=>t.1 • shifts t.2.1 (wordSeq j a t.2.2))).sum

def predictionPolynomial (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) (i : ι) : Polynomial ℝ :=
  (P.map (fun t=>Polynomial.C t.1*Polynomial.X^t.2.1*wordPredictionPolynomial j a t.2.2 i)).sum

def prediction (j : ℝ) (a : ι→ℝ) (z : ℝ) (P : GradedWords ι) (i : ι) : ℝ :=
  (P.map (fun t=>t.1*z^t.2.1*wordPrediction j a z t.2.2 i)).sum

lemma seq_scalar (j c : ℝ) (a : ι→ℝ) : seq j a (scalar c)=ofVector (c • vacuum) := by
  simp only [seq,scalar,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,shifts,
    LinearMap.id_coe,wordSeq,wordOperator]
  funext n
  simp only [Pi.smul_apply,ofVector]
  split_ifs <;> simp_all [ofVector]
lemma seq_append (j : ℝ) (a : ι→ℝ) (P Q : GradedWords ι) :
    seq j a (P++Q)=seq j a P+seq j a Q := by simp [seq]
lemma seq_scale (j c : ℝ) (a : ι→ℝ) (P : GradedWords ι) :
    seq j a (scale c P)=c • seq j a P := by
  induction P with
  | nil => simp [seq,scale]
  | cons t P ih =>
    simp only [scale,List.map_cons,seq,List.sum_cons]
    change (c*t.1) • _+seq j a (scale c P)=c • (t.1 • _+seq j a P)
    rw [ih,smul_add,smul_smul]
lemma seq_bump (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) :
    seq j a (bump P)=shift (seq j a P) := by
  simp [seq,bump,List.map_map,Function.comp_def,shifts,map_list_sum]
lemma seq_prepend (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) (l : WordLetter ι) :
    seq j a (prepend l P)=letterOperator j a l (seq j a P) := by
  simp [seq,prepend,List.map_map,Function.comp_def,wordSeq_cons,map_list_sum,letter_shifts]
lemma predictionPolynomial_eval (j : ℝ) (a : ι→ℝ) (z : ℝ) (P : GradedWords ι) (i : ι) :
    Polynomial.eval z (predictionPolynomial j a P i)=prediction j a z P i := by
  simp only [predictionPolynomial,prediction,polynomial_eval_list_sum,List.map_map,
    Function.comp_def,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [(wordPredictionPolynomial_spec j a _ i).2 z]

end GradedWords

def projectSeries (i : ι) : Seq (ι:=ι)→ₗ[ℝ] PowerSeries ℝ where
  toFun v := PowerSeries.mk (fun n=>project (v n) i)
  map_add' v w := by ext n; simp
  map_smul' c v := by ext n; simp
omit [Fintype ι] in
@[simp] lemma projectSeries_coeff (i : ι) (v : Seq (ι:=ι)) (n : ℕ) :
    PowerSeries.coeff n (projectSeries i v)=project (v n) i := by simp [projectSeries]
omit [Fintype ι] in
lemma projectSeries_shift (i : ι) (v : Seq (ι:=ι)) :
    projectSeries i (shift v)=PowerSeries.X*projectSeries i v := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp
omit [Fintype ι] in
lemma projectSeries_shifts (i : ι) (v : Seq (ι:=ι)) (d : ℕ) :
    projectSeries i (shifts d v)=PowerSeries.X^d*projectSeries i v := by
  induction d with
  | zero => simp [shifts]
  | succ d ih => simp only [shifts,LinearMap.comp_apply,projectSeries_shift,ih,pow_succ']; ring
lemma projectSeries_word (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (hF : inverseCount F≤1) (i : ι) :
    projectSeries i (wordSeq j a F)=(wordPredictionPolynomial j a F i : PowerSeries ℝ) := by
  ext n
  simp only [projectSeries_coeff,Polynomial.coeff_coe,wordSeq_project_coeff j a F hF]

namespace GradedWords

theorem projectSeries_eq (j : ℝ) (a : ι→ℝ) (P : GradedWords ι)
    (hP : ∀ t∈P,inverseCount t.2.2≤1) (i : ι) :
    projectSeries i (seq j a P)=(predictionPolynomial j a P i : PowerSeries ℝ) := by
  induction P with
  | nil => simp [seq,predictionPolynomial]
  | cons t P ih =>
    simp only [seq,predictionPolynomial,List.map_cons,List.sum_cons,map_add,map_smul,
      Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_C,Polynomial.coe_X]
    change _ + projectSeries i (seq j a P)=_+(predictionPolynomial j a P i : PowerSeries ℝ)
    rw [ih (by intro s hs; exact hP s (List.mem_cons_of_mem _ hs)),
      projectSeries_shifts,projectSeries_word j a _ (hP t (by simp))]
    simp [Algebra.smul_def,mul_assoc]

theorem prediction_zero_of_project (j : ℝ) (a : ι→ℝ) (P : GradedWords ι)
    (hP : ∀ t∈P,inverseCount t.2.2≤1) (i : ι)
    (hz : ∀ n,project (seq j a P n) i=0) (z : ℝ) : prediction j a z P i=0 := by
  have hp : predictionPolynomial j a P i=0 := by
    apply Polynomial.ext
    intro n
    have h:=congrArg (PowerSeries.coeff n) (projectSeries_eq j a P hP i)
    simp only [projectSeries_coeff,Polynomial.coeff_coe,hz] at h
    simpa using h.symm
  rw [←predictionPolynomial_eval,hp,Polynomial.eval_zero]
end GradedWords
end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
