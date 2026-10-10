import Mathlib
import OAI.Probability.SKGap.Localization.ClosedPrediction
import OAI.Probability.SKGap.Matrix.RecipeTraceBudget

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.ClosedMarked
open Matrix
variable {n : ℕ}

abbrev Word (n : ℕ) := List (WordLetter (Fin n))
abbrev Polynomial (n : ℕ) := List (ℝ×Word n)
def matrixValue (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (P : Polynomial n) : Matrix (Fin n) (Fin n) ℝ :=
  (P.map (fun t=>t.1 • exactWord j a t.2 J)).sum
def prediction (j : ℝ) (a : Fin n→ℝ) (P : Polynomial n) (i : Fin n) : ℝ :=
  (P.map (fun t=>t.1*wordPrediction j a 1 t.2 i)).sum

def ungrade (P : Primary.Tensor.Series.GradedWords (Fin n)) : Polynomial n :=
  P.map (fun t=>(t.1,t.2.2))
lemma ungrade_matrix (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (P : Primary.Tensor.Series.GradedWords (Fin n)) :
    matrixValue j a J (ungrade P)=Primary.Tensor.Series.GradedWords.matrixValue j a J P := by
  simp [matrixValue,ungrade,Primary.Tensor.Series.GradedWords.matrixValue,List.map_map,Function.comp_def]
lemma ungrade_prediction (j : ℝ) (a : Fin n→ℝ) (P : Primary.Tensor.Series.GradedWords (Fin n)) :
    prediction j a (ungrade P)=Primary.Tensor.Series.GradedWords.prediction j a 1 P := by
  funext i
  simp [prediction,ungrade,Primary.Tensor.Series.GradedWords.prediction,List.map_map,Function.comp_def]

inductive Mark (n : ℕ) where
  | diagonal : Word n→(Fin n→ℝ)→Word n→Mark n
  | average : (Fin n→ℝ)→Word n→Mark n
namespace Mark

def vector : Mark n→Fin n→ℝ
  | .diagonal _ s _ => s
  | .average s _ => s
def word : Mark n→Word n
  | .diagonal P s Q => P++(.diag s::Q)
  | .average _ P => P
def scalar : Mark n→ℝ
  | .diagonal _ _ _ => 1
  | .average s _ => Diagram.mean s
def prepend (P : Word n) : Mark n→Mark n
  | .diagonal Q s R => .diagonal (P++Q) s R
  | .average s Q => .average s (P++Q)
lemma prefix_vector (P : Word n) (t : Mark n) : (t.prepend P).vector=t.vector := by cases t <;> rfl
lemma prefix_scalar (P : Word n) (t : Mark n) : (t.prepend P).scalar=t.scalar := by cases t <;> rfl
lemma prefix_word (P : Word n) (t : Mark n) : (t.prepend P).word=P++t.word := by
  cases t <;> simp [prepend,word,List.append_assoc]
def diagnostic (d : Fin n→ℝ) : Mark n→Word n
  | .diagonal P _ Q => Q++(.diag d::P)
  | .average _ P => P

lemma diagnostic_inverse (d : Fin n→ℝ) (t : Mark n) :
    inverseCount (t.diagnostic d)=inverseCount t.word := by
  cases t <;> simp [diagnostic,word,inverseCount,List.countP_append,Nat.add_comm]

lemma trace_error (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0<n) (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (t : Mark n)
    (ht : inverseCount t.word≤1) {B : ℝ} (hB : 0≤B)
    (hb : diagonalSeminorm (exactWord j a (t.diagnostic d) J-
      Matrix.diagonal (wordPrediction j a 1 (t.diagnostic d)))≤B) :
    |t.scalar*(trace (Matrix.diagonal d*exactWord j a t.word J)-
      ∑i,d i*wordPrediction j a 1 t.word i)|≤SKGapCutoff.Recipe.vectorNorm t.vector*B := by
  cases t with
  | diagonal P s Q =>
    simpa only [scalar,one_mul,word,diagnostic,vector,SKGapCutoff.Recipe.vectorNorm] using
      (rotated_small_word_trace_error j a d s J P Q ht).trans
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  | average s P =>
    have H:=trace_small_diagonal_error d (wordPrediction j a 1 P) (exactWord j a P J)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left H (abs_nonneg _)).trans (by
      change |Diagram.mean s| *(SKGapCutoff.Recipe.vectorNorm d*_)≤SKGapCutoff.Recipe.vectorNorm s*B
      calc
        _ ≤ |Diagram.mean s| *(SKGapCutoff.Recipe.vectorNorm d*B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (abs_nonneg _)
        _ = (|Diagram.mean s| *SKGapCutoff.Recipe.vectorNorm d)*B := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Primary.SmallMark.average_norm_product hn s d hd) hB)
end Mark

abbrev Marked (n : ℕ) := List (ℝ×Mark n)
namespace Marked

def plain (P : Marked n) : Polynomial n := P.map (fun t=>(t.1*t.2.scalar,t.2.word))
def budget (P : Marked n) : ℝ := (P.map (fun t=>|t.1| *SKGapCutoff.Recipe.vectorNorm t.2.vector)).sum
def prepend (F : Word n) (P : Marked n) : Marked n := P.map (fun t=>(t.1,t.2.prepend F))
def scale (c : ℝ) (P : Marked n) : Marked n := P.map (fun t=>(c*t.1,t.2))
lemma plain_prefix (F : Word n) (P : Marked n) :
    (P.prepend F).plain=P.plain.map (fun t=>(t.1,F++t.2)) := by
  simp [prepend,plain,List.map_map,Function.comp_def,Mark.prefix_scalar,Mark.prefix_word]
lemma plain_scale (c : ℝ) (P : Marked n) : (P.scale c).plain=P.plain.map (fun t=>(c*t.1,t.2)) := by
  simp [scale,plain,List.map_map,Function.comp_def,mul_assoc]
lemma plain_append (P Q : Marked n) : (P++Q).plain=P.plain++Q.plain := by simp [plain]
lemma budget_prefix (F : Word n) (P : Marked n) : (P.prepend F).budget=P.budget := by
  simp [prepend,budget,List.map_map,Function.comp_def,Mark.prefix_vector]
lemma budget_scale (c : ℝ) (P : Marked n) : (P.scale c).budget=|c| *P.budget := by
  induction P with
  | nil => simp [scale,budget]
  | cons t P ih => simp [scale,budget,abs_mul,mul_assoc,mul_add] at *;exact ih
lemma budget_append (P Q : Marked n) : (P++Q).budget=P.budget+Q.budget := by simp [budget]
lemma budget_nonneg (P : Marked n) : 0≤P.budget := by
  apply List.sum_nonneg; intro r hr; obtain ⟨t,_,rfl⟩:=List.mem_map.mp hr
  exact mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem trace_error (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (P : Marked n)
    (hI : ∀t∈P,inverseCount t.2.word≤1) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈P,diagonalSeminorm (exactWord j a (t.2.diagnostic d) J-
      Matrix.diagonal (wordPrediction j a 1 (t.2.diagnostic d)))≤B) :
    |trace (Matrix.diagonal d*matrixValue j a J P.plain)-
      ∑i,d i*prediction j a P.plain i|≤P.budget*B := by
  induction P with
  | nil => simp [plain,budget,matrixValue,prediction]
  | cons t P ih =>
    have ht:=Mark.trace_error j a J hn d hd t.2 (hI t (by simp)) hB (hb t (by simp))
    have hh:=ih (fun s hs=>hI s (List.mem_cons_of_mem _ hs)) (fun s hs=>hb s (List.mem_cons_of_mem _ hs))
    simp only [plain,List.map_cons,matrixValue,List.sum_cons,prediction,budget] at *
    simp only [mul_add,mul_smul_comm,trace_add,trace_smul,smul_eq_mul,Finset.sum_add_distrib,add_mul]
    have he : (∑i,d i*(t.1*t.2.scalar*wordPrediction j a 1 t.2.word i))=
        t.1*t.2.scalar*(∑i,d i*wordPrediction j a 1 t.2.word i) := by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
    rw [he]
    have hc:=mul_le_mul_of_nonneg_left ht (abs_nonneg t.1)
    rw [←abs_mul] at hc
    calc
      _ = |t.1*(t.2.scalar*(trace (Matrix.diagonal d*exactWord j a t.2.word J)-
            ∑i,d i*wordPrediction j a 1 t.2.word i))+
          (trace (Matrix.diagonal d*(List.map (fun p=>p.1 • exactWord j a p.2 J)
            (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)-
            ∑i,d i*(List.map (fun p=>p.1*wordPrediction j a 1 p.2 i)
              (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)| := by congr 1;ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (by convert! hc using 1; ring) hh)
end Marked
end SKGap.Noncrossing.ClosedMarked

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.ClosedMarked
open Matrix Primary Primary.Tensor.Series
variable {n : ℕ}

lemma ungrade_append (P Q : GradedWords (Fin n)) : ungrade (P++Q)=ungrade P++ungrade Q := by simp [ungrade]
lemma ungrade_bump (P : GradedWords (Fin n)) : ungrade (GradedWords.bump P)=ungrade P := by
  simp [ungrade,GradedWords.bump,List.map_map,Function.comp_def]
lemma ungrade_prepend (l : WordLetter (Fin n)) (P : GradedWords (Fin n)) :
    ungrade (GradedWords.prepend l P)=(ungrade P).map (fun t=>(t.1,l::t.2)) := by
  simp [ungrade,GradedWords.prepend,List.map_map,Function.comp_def]
lemma ungrade_scale (c : ℝ) (P : GradedWords (Fin n)) :
    ungrade (GradedWords.scale c P)=(ungrade P).map (fun t=>(c*t.1,t.2)) := by
  simp [ungrade,GradedWords.scale,List.map_map,Function.comp_def]

namespace Marked

def diagonalWords (s : Fin n→ℝ) (P : GradedWords (Fin n)) : Marked n :=
  P.map (fun t=>(t.1,Mark.diagonal [] s t.2.2))
def averageWords (c : ℝ) (s : Fin n→ℝ) (P : GradedWords (Fin n)) : Marked n :=
  P.map (fun t=>(c*t.1,Mark.average s t.2.2))
def mass (P : GradedWords (Fin n)) : ℝ := (P.map (fun t=>|t.1|)).sum
lemma plain_diagonalWords (s : Fin n→ℝ) (P : GradedWords (Fin n)) :
    (diagonalWords s P).plain=ungrade (GradedWords.prepend (.diag s) P) := by
  simp [diagonalWords,plain,ungrade,GradedWords.prepend,List.map_map,Function.comp_def,Mark.scalar,Mark.word]
lemma plain_averageWords (c : ℝ) (s : Fin n→ℝ) (P : GradedWords (Fin n)) :
    (averageWords c s P).plain=ungrade (GradedWords.scale (c*Diagram.mean s) P) := by
  simp only [averageWords,plain,ungrade,GradedWords.scale,List.map_map,Function.comp_def,Mark.scalar,Mark.word]
  congr 1;funext t;congr 1;ring
lemma budget_diagonalWords (s : Fin n→ℝ) (P : GradedWords (Fin n)) :
    (diagonalWords s P).budget=SKGapCutoff.Recipe.vectorNorm s*mass P := by
  induction P with
  | nil => simp [diagonalWords,budget,mass]
  | cons t P ih =>
    simp only [diagonalWords,List.map_cons,budget,List.sum_cons,Mark.vector,mass] at *
    rw [ih];ring
lemma budget_averageWords (c : ℝ) (s : Fin n→ℝ) (P : GradedWords (Fin n)) :
    (averageWords c s P).budget=|c| *SKGapCutoff.Recipe.vectorNorm s*mass P := by
  induction P with
  | nil => simp [averageWords,budget,mass]
  | cons t P ih =>
    simp only [averageWords,List.map_cons,budget,List.sum_cons,Mark.vector,mass,abs_mul] at *
    rw [ih];ring

lemma bounded_of_plain (P : Marked n) (Q : GradedWords (Fin n)) (h : P.plain=ungrade Q)
    (hQ : GradedWords.bounded 1 Q) : ∀t∈P,inverseCount t.2.word≤1 := by
  intro t ht
  have hp : (t.1*t.2.scalar,t.2.word)∈ungrade Q := h ▸ List.mem_map.mpr ⟨t,ht,rfl⟩
  obtain ⟨q,hq,he⟩:=List.mem_map.mp hp
  have hword : q.2.2=t.2.word := congrArg Prod.snd he
  rw [←hword]
  exact hQ q hq
end Marked

abbrev Pair (n : ℕ) := Marked n×Marked n
def pairPlain (P : Pair n) : Polynomial n×Polynomial n := (P.1.plain,P.2.plain)
def pairUngrade (P : GradedWords (Fin n)×GradedWords (Fin n)) := (ungrade P.1,ungrade P.2)
def zeroPair : Pair n := ([(0,.average 0 [])],[(0,.average 0 [.noise])])
lemma zeroPair_plain (j : ℝ) : pairPlain (zeroPair (n:=n))=pairUngrade (GradedWords.ordinaryWords j (.leaf 0)) := by
  simp [pairPlain,pairUngrade,zeroPair,Marked.plain,Mark.scalar,Mark.word,GradedWords.ordinaryWords,
    GradedWords.scalar,GradedWords.bump,GradedWords.prepend,ungrade]

def implicitPair (j : ℝ) (a p : Fin n→ℝ) (t : SourceTree (Fin n→ℝ)) : Pair n :=
  let T:=GradedWords.ordinaryWords j t
  let S:=(Marked.diagonalWords p T.2).prepend [.inverse]++
    (Marked.averageWords (-j) p T.1).prepend [.inverse,.diag a]
  (S,(S.prepend [.noise]++S.scale (-(j*Diagram.mean a)))++Marked.averageWords (-j) p T.1)

lemma implicitPair_plain (j : ℝ) (a p : Fin n→ℝ) (t : SourceTree (Fin n→ℝ)) :
    pairPlain (implicitPair j a p t)=pairUngrade (GradedWords.implicitSource j a p t,GradedWords.implicitField j a p t) := by
  have hs : (implicitPair j a p t).1.plain=ungrade (GradedWords.implicitSource j a p t) := by
    simp only [implicitPair,Marked.plain_append,Marked.plain_prefix,Marked.plain_diagonalWords,
      Marked.plain_averageWords,GradedWords.implicitSource,ungrade_prepend,ungrade_append,
      ungrade_scale,ungrade_bump,List.map_append,List.map_map,Function.comp_def,
      List.cons_append,List.nil_append,neg_mul]
  apply Prod.ext hs
  dsimp only [pairPlain,pairUngrade]
  change ((implicitPair j a p t).1.prepend [.noise]++
    (implicitPair j a p t).1.scale (-(j*Diagram.mean a))++Marked.averageWords (-j) p (GradedWords.ordinaryWords j t).1).plain=_
  rw [Marked.plain_append,Marked.plain_append,Marked.plain_prefix,Marked.plain_scale,hs,Marked.plain_averageWords]
  simp [GradedWords.implicitField,ungrade_append,ungrade_bump,ungrade_scale,ungrade_prepend,neg_mul]

def smallBranch (j : ℝ) (p : Fin n→ℝ) (T : GradedWords (Fin n)×GradedWords (Fin n)) (V : Pair n) : Pair n :=
  (Marked.diagonalWords p T.2++V.1,
    ((Marked.diagonalWords p T.2).prepend [.noise]++Marked.averageWords (-j) p T.1)++V.2)
def boundedBranch (j : ℝ) (p : Fin n→ℝ) (U V : Pair n) : Pair n :=
  (U.2.prepend [.diag p]++V.1,
    (U.2.prepend [.noise,.diag p]++U.1.scale (-(j*Diagram.mean p)))++V.2)
lemma smallBranch_plain (j : ℝ) (p : Fin n→ℝ) (T V : GradedWords (Fin n)×GradedWords (Fin n))
    (Q : Pair n) (hQ : pairPlain Q=pairUngrade V) :
    pairPlain (smallBranch j p T Q)=pairUngrade (GradedWords.branch j p T V) := by
  have h₁ : Q.1.plain=ungrade V.1 := congrArg Prod.fst hQ
  have h₂ : Q.2.plain=ungrade V.2 := congrArg Prod.snd hQ
  simp [pairPlain,smallBranch,Marked.plain_append,Marked.plain_prefix,Marked.plain_diagonalWords,
    Marked.plain_averageWords,h₁,h₂,pairUngrade,GradedWords.branch,ungrade_append,ungrade_bump,
    ungrade_prepend,ungrade_scale,List.map_map,Function.comp_def,neg_mul]
lemma boundedBranch_plain (j : ℝ) (p : Fin n→ℝ) (T V : GradedWords (Fin n)×GradedWords (Fin n))
    (P Q : Pair n) (hP : pairPlain P=pairUngrade T) (hQ : pairPlain Q=pairUngrade V) :
    pairPlain (boundedBranch j p P Q)=pairUngrade (GradedWords.branch j p T V) := by
  have h₁ : P.1.plain=ungrade T.1 := congrArg Prod.fst hP
  have h₂ : P.2.plain=ungrade T.2 := congrArg Prod.snd hP
  have h₃ : Q.1.plain=ungrade V.1 := congrArg Prod.fst hQ
  have h₄ : Q.2.plain=ungrade V.2 := congrArg Prod.snd hQ
  simp [pairPlain,boundedBranch,Marked.plain_append,Marked.plain_prefix,Marked.plain_scale,
    h₁,h₂,h₃,h₄,pairUngrade,GradedWords.branch,ungrade_append,ungrade_bump,ungrade_prepend,
    ungrade_scale,List.map_map,Function.comp_def]

inductive SmallTree (n : ℕ) where
  | zero
  | implicit : (Fin n→ℝ)→SourceTree (Fin n→ℝ)→SmallTree n
  | small : (Fin n→ℝ)→ClosedTree (Fin n→ℝ)→SmallTree n→SmallTree n
  | bounded : (Fin n→ℝ)→SmallTree n→SmallTree n→SmallTree n
namespace SmallTree

def tree : SmallTree n→ClosedTree (Fin n→ℝ)
  | .zero=>.leaf 0
  | .implicit p T=>.implicit p T
  | .small p T V=>.branch p T V.tree
  | .bounded p T V=>.branch p T.tree V.tree
def marked (j : ℝ) (a : Fin n→ℝ) : SmallTree n→Pair n
  | .zero=>zeroPair
  | .implicit p T=>implicitPair j a p T
  | .small p T V=>smallBranch j p (T.words j a) (V.marked j a)
  | .bounded p T V=>boundedBranch j p (T.marked j a) (V.marked j a)
lemma leafMass (T : SmallTree n) : T.tree.leafMass=0 := by
  induction T with
  | zero=>rfl
  | implicit=>rfl
  | small p U V ih=>exact ih
  | bounded p U V ih1 ih2=>exact ih2
lemma plain (j : ℝ) (a : Fin n→ℝ) (T : SmallTree n) :
    pairPlain (T.marked j a)=pairUngrade (T.tree.words j a) := by
  induction T with
  | zero=>exact zeroPair_plain j
  | implicit p U=>exact implicitPair_plain j a p U
  | small p U V ih=>exact smallBranch_plain j p (U.words j a) (V.tree.words j a) (V.marked j a) ih
  | bounded p U V ih1 ih2 =>
    exact boundedBranch_plain j p (U.tree.words j a) (V.tree.words j a)
      (U.marked j a) (V.marked j a) ih1 ih2

theorem diagonal (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (T : SmallTree n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[ (T.marked j a).1,(T.marked j a).2 ],∀t∈P,
      diagonalSeminorm (exactWord j a (t.2.diagnostic d) J-
        Matrix.diagonal (wordPrediction j a 1 (t.2.diagnostic d)))≤B) :
    (∑i,|GradedWords.matrixValue j a J (T.tree.words j a).1 i i|)≤(T.marked j a).1.budget*B ∧
    (∑i,|GradedWords.matrixValue j a J (T.tree.words j a).2 i i|)≤(T.marked j a).2.budget*B := by
  have hs : (T.marked j a).1.plain=ungrade (T.tree.words j a).1 := congrArg Prod.fst (T.plain j a)
  have hf : (T.marked j a).2.plain=ungrade (T.tree.words j a).2 := congrArg Prod.snd (T.plain j a)
  have hbound (P : Marked n) (Q : GradedWords (Fin n)) (hp : P.plain=ungrade Q)
      (hQ : GradedWords.bounded 1 Q) (hz : ∀i,GradedWords.prediction j a 1 Q i=0)
      (hP : P∈[(T.marked j a).1,(T.marked j a).2]) :
      (∑i,|GradedWords.matrixValue j a J Q i i|)≤P.budget*B := by
    apply diagonal_abs_sum_of_tests
    intro d hd
    have H:=Marked.trace_error j a J hn d hd P (P.bounded_of_plain Q hp hQ) hB (hb d hd P hP)
    rw [hp,ungrade_matrix,ungrade_prediction] at H
    simpa only [hz,mul_zero,Finset.sum_const_zero,sub_zero] using H
  exact ⟨hbound _ _ hs (T.tree.words_bounded j a).1 (T.tree.source_prediction_zero j a T.leafMass 1) (by simp),
    hbound _ _ hf (T.tree.words_bounded j a).2 (T.tree.field_prediction_zero j a 1) (by simp)⟩
end SmallTree
end SKGap.Noncrossing.ClosedMarked

end
end

end OAI
