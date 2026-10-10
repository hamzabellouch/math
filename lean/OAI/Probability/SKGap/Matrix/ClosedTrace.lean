import Mathlib
import OAI.Probability.SKGap.Localization.Operation
import OAI.Probability.SKGap.Localization.CyclicPrediction
import OAI.Probability.SKGap.Matrix.WordFockSeries
import OAI.Probability.SKGap.Localization.ClosedPrediction

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exactWord_append (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P Q : List (WordLetter ι)) :
    exactWord j a (P++Q) J=exactWord j a P J*exactWord j a Q J := by
  induction P with
  | nil => simp [exactWord,matrixFactorProduct]
  | cons l P ih =>
    change l.exactEval j a J*exactWord j a (P++Q) J=
      (l.exactEval j a J*exactWord j a P J)*exactWord j a Q J
    rw [ih,mul_assoc]
lemma exactWord_diag (j : ℝ) (a d : ι→ℝ) (J : Matrix ι ι ℝ) (F : List (WordLetter ι)) :
    exactWord j a (.diag d::F) J=Matrix.diagonal d*exactWord j a F J := rfl

omit [DecidableEq ι] in
lemma wordPrediction_diag (j : ℝ) (a d : ι→ℝ) (z : ℝ) (F : List (WordLetter ι))
    (hF : inverseCount F≤1) (i : ι) :
    wordPrediction j a z (.diag d::F) i=d i*wordPrediction j a z F i := by
  have hp : wordPredictionPolynomial j a (.diag d::F) i=
      Polynomial.C (d i)*wordPredictionPolynomial j a F i := by
    apply Polynomial.ext
    intro n
    rw [←Primary.Tensor.Series.wordSeq_project_coeff j a (.diag d::F) (show inverseCount (.diag d::F)≤1 from hF),
      Polynomial.coeff_C_mul,←Primary.Tensor.Series.wordSeq_project_coeff j a F hF,
      Primary.Tensor.Series.wordSeq_cons]
    rfl
  have h:=congrArg (Polynomial.eval z) hp
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,
    fun F i=>(wordPredictionPolynomial_spec j a F i).2 z] using h

lemma trace_small_diagonal_error (s v : ι→ℝ) (Q : Matrix ι ι ℝ) :
    |trace (Matrix.diagonal s*Q)-∑ i,s i*v i|≤
      ‖(WithLp.toLp 2 s : EuclideanSpace ℝ ι)‖*diagonalSeminorm (Q-Matrix.diagonal v) := by
  have h:=abs_real_inner_le_norm (WithLp.toLp 2 s : EuclideanSpace ℝ ι)
    (diagonalVector (Q-Matrix.diagonal v))
  simpa only [trace,diag,Matrix.diagonal_mul,Matrix.sub_apply,Matrix.diagonal_apply_eq,
    diagonalVector,PiLp.inner_apply,Real.inner_apply,PiLp.toLp_apply,
    mul_sub,Finset.sum_sub_distrib,diagonalSeminorm] using h

theorem rotated_small_word_trace_error (j : ℝ) (a d s : ι→ℝ) (J : Matrix ι ι ℝ)
    (P Q : List (WordLetter ι)) (hF : inverseCount (P++(.diag s::Q))≤1) :
    |trace (Matrix.diagonal d*exactWord j a (P++(.diag s::Q)) J)-
      ∑ i,d i*wordPrediction j a 1 (P++(.diag s::Q)) i|≤
      ‖(WithLp.toLp 2 s : EuclideanSpace ℝ ι)‖*
        diagonalSeminorm (exactWord j a (Q++(.diag d::P)) J-
          Matrix.diagonal (wordPrediction j a 1 (Q++(.diag d::P)))) := by
  have hrot : inverseCount (Q++(.diag d::P))≤1 := by
    simp only [inverseCount_append] at hF ⊢
    change inverseCount Q+inverseCount P≤1
    change inverseCount P+inverseCount Q≤1 at hF
    omega
  have hc : (∑ i,d i*wordPrediction j a 1 (P++(.diag s::Q)) i)=
      ∑ i,s i*wordPrediction j a 1 (Q++(.diag d::P)) i := by
    have h0 : inverseCount ((.diag d::P)++(.diag s::Q))≤1 := hF
    have h:=wordPrediction_mean_cyclic j a 1 (.diag d::P) (.diag s::Q) h0
    simpa only [List.cons_append,wordPrediction_diag j a d 1 _ hF,
      wordPrediction_diag j a s 1 _ hrot] using h
  rw [hc,exactWord_append,exactWord_diag,←mul_assoc,
    trace_mul_comm (Matrix.diagonal d*exactWord j a P J),mul_assoc]
  rw [←exactWord_diag,←exactWord_append]
  exact trace_small_diagonal_error s _ _

namespace Primary.Tensor.Series.GradedWords

def matrixValue (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) : Matrix ι ι ℝ :=
  (P.map (fun t=>t.1 • exactWord j a t.2.2 J)).sum

lemma trace_list_error (j : ℝ) (a d : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι)
    (b : List (WordLetter ι)→ℝ)
    (h : ∀ t∈P,|trace (Matrix.diagonal d*exactWord j a t.2.2 J)-
        ∑ i,d i*wordPrediction j a 1 t.2.2 i|≤b t.2.2) :
    |trace (Matrix.diagonal d*matrixValue j a J P)-∑ i,d i*prediction j a 1 P i|≤
      (P.map (fun t=>|t.1| *b t.2.2)).sum := by
  induction P with
  | nil => simp [matrixValue,prediction]
  | cons t P ih =>
    have ht:=h t (by simp)
    have hP:=ih (by intro s hs; exact h s (List.mem_cons_of_mem _ hs))
    simp only [matrixValue,prediction,List.map_cons,List.sum_cons] at *
    simp only [one_pow,mul_one] at *
    simp only [mul_add,mul_smul_comm,trace_add,trace_smul,smul_eq_mul,
      Finset.sum_add_distrib]
    have he : (∑ i,d i*(t.1*wordPrediction j a 1 t.2.2 i))=
        t.1*(∑ i,d i*wordPrediction j a 1 t.2.2 i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]
    have ha := abs_add_le
      (t.1*(trace (Matrix.diagonal d*exactWord j a t.2.2 J)-∑ i,d i*wordPrediction j a 1 t.2.2 i))
      (trace (Matrix.diagonal d*(List.map (fun t=>t.1 • exactWord j a t.2.2 J) P).sum)-
        ∑ i,d i*(List.map (fun t=>t.1*wordPrediction j a 1 t.2.2 i) P).sum)
    rw [abs_mul] at ha
    calc
      _ = |t.1*(trace (Matrix.diagonal d*exactWord j a t.2.2 J)-∑ i,d i*wordPrediction j a 1 t.2.2 i)+
          (trace (Matrix.diagonal d*(List.map (fun t=>t.1 • exactWord j a t.2.2 J) P).sum)-
          ∑ i,d i*(List.map (fun t=>t.1*wordPrediction j a 1 t.2.2 i) P).sum)| := by congr 1; ring
      _ ≤ _ := ha.trans (add_le_add (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hP)

theorem closed_source_trace_bound (j : ℝ) (a d : ι→ℝ) (J : Matrix ι ι ℝ)
    (t : ClosedTree (ι→ℝ)) (ht : t.leafMass=0) (b : List (WordLetter ι)→ℝ)
    (h : ∀ w∈(t.words j a).1,|trace (Matrix.diagonal d*exactWord j a w.2.2 J)-
        ∑ i,d i*wordPrediction j a 1 w.2.2 i|≤b w.2.2) :
    |trace (Matrix.diagonal d*matrixValue j a J (t.words j a).1)|≤
      ((t.words j a).1.map (fun w=>|w.1| *b w.2.2)).sum := by
  have H:=trace_list_error j a d J (t.words j a).1 b h
  simpa only [t.source_prediction_zero j a ht, mul_zero,Finset.sum_const_zero,sub_zero] using H
end Primary.Tensor.Series.GradedWords
end SKGap.Noncrossing

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.Primary
open Diagram WordSeries Matrix
variable {n : ℕ}

inductive SmallMark (n : ℕ) where
  | diagonal : List (Letter (Fin n→ℝ))→(Fin n→ℝ)→List (Letter (Fin n→ℝ))→SmallMark n
  | average : (Fin n→ℝ)→List (Letter (Fin n→ℝ))→SmallMark n

namespace SmallMark

def vector : SmallMark n→Fin n→ℝ
  | .diagonal _ s _ => s
  | .average s _ => s

def word : SmallMark n→List (Letter (Fin n→ℝ))
  | .diagonal P s Q => P++(.diag s::Q)
  | .average _ P => P

def scalar : SmallMark n→ℝ
  | .diagonal _ _ _ => 1
  | .average s _ => Diagram.mean s

def prepend (P : List (Letter (Fin n→ℝ))) : SmallMark n→SmallMark n
  | .diagonal Q s R => .diagonal (P++Q) s R
  | .average s Q => .average s (P++Q)

lemma prefix_vector (P : List (Letter (Fin n→ℝ))) (t : SmallMark n) : (t.prepend P).vector=t.vector := by cases t <;> rfl
lemma prefix_scalar (P : List (Letter (Fin n→ℝ))) (t : SmallMark n) : (t.prepend P).scalar=t.scalar := by cases t <;> rfl
lemma prefix_word (P : List (Letter (Fin n→ℝ))) (t : SmallMark n) : (t.prepend P).word=P++t.word := by
  cases t <;> simp [prepend,word,List.append_assoc]

def diagnostic (d : Fin n→ℝ) : SmallMark n→List (Letter (Fin n→ℝ))
  | .diagonal P _ Q => Q++(.diag d::P)
  | .average _ P => P

lemma average_norm_product (hn : 0<n) (s d : Fin n→ℝ) (hd : ∀i,|d i|≤1) :
    |Diagram.mean s| * SKGapCutoff.Recipe.vectorNorm d ≤ SKGapCutoff.Recipe.vectorNorm s := by
  have H:=SKGapCutoff.Recipe.primary_mean_size (fun _=>s) (fun _=>d) (fun _=>false) hn
    (fun i=>hd i)
  change SKGapCutoff.Recipe.vectorNorm ((SKGapCutoff.Primary.siteMean (fun _=>s) (fun _=>false)) • d)≤_ at H
  rw [SKGapCutoff.Recipe.vectorNorm_smul] at H
  simpa only [SKGapCutoff.Primary.siteMean,Diagram.mean,Fintype.card_fin] using H

lemma rotated_trace_error (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (d s : Fin n→ℝ)
    (P Q : List (Letter (Fin n→ℝ))) :
    |trace (Matrix.diagonal d*matrixWord J (P++(.diag s::Q)))-
      ∑i,d i*Diagram.prediction j (P++(.diag s::Q)) i| ≤
      SKGapCutoff.Recipe.vectorNorm s * diagonalSeminorm
        (matrixWord J (Q++(.diag d::P))-Matrix.diagonal (Diagram.prediction j (Q++(.diag d::P)))) := by
  have h1 : liftWord P++(.diag s::liftWord Q)=liftWord (P++(.diag s::Q)) := by simp [liftWord,Letter.toWord]
  have h2 : liftWord Q++(.diag d::liftWord P)=liftWord (Q++(.diag d::P)) := by simp [liftWord,Letter.toWord]
  have H:=rotated_small_word_trace_error j (fun _:Fin n=>0) d s J (liftWord P) (liftWord Q)
    (by rw [h1,inverseCount_lift]; omega)
  rw [h1,h2,exactWord_lift,exactWord_lift] at H
  have he : wordPrediction j (fun _:Fin n=>0) 1 (liftWord (Q++(.diag d::P)))=
      Diagram.prediction j (Q++(.diag d::P)) := by funext i; exact wordPrediction_lift ..
  rw [he] at H
  simpa only [wordPrediction_lift,SKGapCutoff.Recipe.vectorNorm] using H

theorem trace_error (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (t : SmallMark n) {B : ℝ} (hB : 0≤B)
    (hb : diagonalSeminorm (matrixWord J (t.diagnostic d)-
      Matrix.diagonal (Diagram.prediction j (t.diagnostic d)))≤B) :
    |t.scalar*(trace (Matrix.diagonal d*matrixWord J t.word)-
      ∑i,d i*Diagram.prediction j t.word i)| ≤ SKGapCutoff.Recipe.vectorNorm t.vector*B := by
  cases t with
  | diagonal P s Q =>
    simpa only [scalar,one_mul,word,diagnostic,vector] using
      (rotated_trace_error j J d s P Q).trans
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  | average s P =>
    have H:=trace_small_diagonal_error d (Diagram.prediction j P) (matrixWord J P)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left H (abs_nonneg _)).trans
      (by
        change |Diagram.mean s| * (SKGapCutoff.Recipe.vectorNorm d*_)≤SKGapCutoff.Recipe.vectorNorm s*B
        calc
          _ ≤ |Diagram.mean s| *(SKGapCutoff.Recipe.vectorNorm d*B) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (abs_nonneg _)
          _ = (|Diagram.mean s| * SKGapCutoff.Recipe.vectorNorm d)*B := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (average_norm_product hn s d hd) hB)

end SmallMark

abbrev MarkedPolynomial (n : ℕ) := List (ℝ×SmallMark n)
namespace MarkedPolynomial

def plain (P : MarkedPolynomial n) : WordPolynomial (ι:=Fin n) :=
  P.map (fun t=>(t.1*t.2.scalar,t.2.word))
def budget (P : MarkedPolynomial n) : ℝ :=
  (P.map (fun t=>|t.1| *SKGapCutoff.Recipe.vectorNorm t.2.vector)).sum

def prepend (F : List (Letter (Fin n→ℝ))) (P : MarkedPolynomial n) : MarkedPolynomial n :=
  P.map (fun t=>(t.1,t.2.prepend F))
def scale (c : ℝ) (P : MarkedPolynomial n) : MarkedPolynomial n := P.map (fun t=>(c*t.1,t.2))

lemma plain_prefix (F : List (Letter (Fin n→ℝ))) (P : MarkedPolynomial n) :
    (P.prepend F).plain=prependWords F P.plain := by
  simp [prepend,plain,prependWords,List.map_map,Function.comp_def,SmallMark.prefix_scalar,SmallMark.prefix_word]
lemma plain_scale (c : ℝ) (P : MarkedPolynomial n) : (P.scale c).plain=Primary.scale c P.plain := by
  simp [scale,plain,Primary.scale,List.map_map,Function.comp_def,mul_assoc]
lemma plain_append (P Q : MarkedPolynomial n) : (P++Q).plain=P.plain++Q.plain := by simp [plain]
lemma budget_prefix (F : List (Letter (Fin n→ℝ))) (P : MarkedPolynomial n) : (P.prepend F).budget=P.budget := by
  simp [prepend,budget,List.map_map,Function.comp_def,SmallMark.prefix_vector]
lemma budget_scale (c : ℝ) (P : MarkedPolynomial n) : (P.scale c).budget=|c| *P.budget := by
  induction P with
  | nil => simp [scale,budget]
  | cons t P ih => simp [scale,budget,abs_mul,mul_assoc,mul_add] at *; exact ih
lemma budget_append (P Q : MarkedPolynomial n) : (P++Q).budget=P.budget+Q.budget := by simp [budget]

theorem trace_error (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (P : MarkedPolynomial n) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈P,diagonalSeminorm (matrixWord J (t.2.diagnostic d)-
      Matrix.diagonal (Diagram.prediction j (t.2.diagnostic d)))≤B) :
    |trace (Matrix.diagonal d*matrixPolynomial J P.plain)-
      ∑i,d i*polynomialPrediction j P.plain i|≤P.budget*B := by
  induction P with
  | nil => simp [plain,budget,matrixPolynomial,polynomialPrediction]
  | cons t P ih =>
    have ht:=SmallMark.trace_error j J hn d hd t.2 hB (hb t (by simp))
    have hh:=ih (fun s hs=>hb s (List.mem_cons_of_mem _ hs))
    simp only [plain,List.map_cons,matrixPolynomial,List.sum_cons,polynomialPrediction,budget] at *
    simp only [mul_add,mul_smul_comm,trace_add,trace_smul,smul_eq_mul,Finset.sum_add_distrib,add_mul]
    have he : (∑i,d i*(t.1*t.2.scalar*Diagram.prediction j t.2.word i))=
        t.1*t.2.scalar*(∑i,d i*Diagram.prediction j t.2.word i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]
    have hc:=mul_le_mul_of_nonneg_left ht (abs_nonneg t.1)
    rw [←abs_mul] at hc
    calc
      _ = |t.1*(t.2.scalar*(trace (Matrix.diagonal d*matrixWord J t.2.word)-
            ∑i,d i*Diagram.prediction j t.2.word i))+
          (trace (Matrix.diagonal d*(List.map (fun p=>p.1 • matrixWord J p.2)
            (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)-
            ∑i,d i*(List.map (fun p=>p.1*Diagram.prediction j p.2 i)
              (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (by convert! hc using 1; ring) hh)

end MarkedPolynomial
end SKGap.Noncrossing.Primary

end
end

end OAI
