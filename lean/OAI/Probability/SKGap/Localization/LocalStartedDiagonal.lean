import Mathlib
import OAI.Probability.SKGap.Matrix.ClosedErrorTrace
import OAI.Probability.SKGap.Localization.StartedMarked
import OAI.Probability.SKGap.Stability.LocalStartedImplicit

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ} {ι κ σ κ₀ σ₀ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable (D : OrdinaryData n ι κ σ) (I : OrdinaryData n Unit κ₀ σ₀)
variable (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ)) (t : SourceTree (Fin n→ℝ))

theorem implicit_started_diagonal_local (hj : D.j=I.j) (hJ : D.J=I.J)
    (x : Spin n)
    (hW : w x=I.sourceOf 1 (fun _=>y) x)
    (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i)) (hn : 0<n)
    (ha0 : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef)
    {C F A R M B : ℝ} {Cs Cf : ℕ→ℝ} {N : ℕ}
    (hP : TraceControl (I.implicitSourcePrimitive t y x) C)
    (hQ : TraceControl (I.implicitFieldPrimitive t w y x) F)
    (hR : 0≤R) (hM : 0≤M) (hB : 0≤B) (hA : 1≤A) (ha : ∀i,|I.implicitCoefficient x i|≤A)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
    (hw : ClosedWordTestBound D.j (I.implicitCoefficient x) D.J A M (2*N+5))
    (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1,
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2],∀v∈P,
      diagonalSeminorm (exactWord D.j (I.implicitCoefficient x) (v.2.diagnostic d) D.J-
        Matrix.diagonal (wordPrediction D.j (I.implicitCoefficient x) 1 (v.2.diagnostic d)))≤B) :
    let q:=I.j*siteMean I.implicitCoefficient x
    let Bs:=fun a=>if a=0 then C+F else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
    ∀a≤N,
      (∑i,|derivativeMatrix (D.startedSource w y a) x i i|)≤
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1.budget*B+
        (errorBudget R Bs Bf a).1*M ∧
      (∑i,|derivativeMatrix (D.startedAuxiliary w y a) x i i|)≤
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2.budget*B+
        (errorBudget R Bs Bf a).2*M := by
  have H:=D.implicit_started_error_words_local I w y T t hj hJ x hW hWf hY hYf ha0 hS hP hQ hR hM ha hp hr hs hf
    (L:=2*N+3) (by simpa only [Nat.add_assoc] using hw)
  dsimp only at H ⊢
  intro a haN
  let t₀:SmallTree n:=.implicit (I.implicitPartial y x) t
  let a₀:=I.implicitCoefficient x
  have hret:=D.started_retained_diagonal w y T t₀ a₀ x a hn hB (hd a haN)
  have hword (d : Fin n→ℝ) (hd' : ∀i,|d i|≤1) : wordBounded A [.diag d] := by
    intro l hl
    have he:l=Letter.diag d:=List.mem_singleton.mp hl
    subst l
    exact fun i=>(hd' i).trans hA
  have herrorS : (∑i,|D.startedSourceError w y T t₀.tree a₀ x a i i|)≤
      (errorBudget R (fun a=>if a=0 then C+F else Cs a)
        (fun a=>if a=0 then |I.j*siteMean I.implicitCoefficient x| *(C+F)+F else Cf a) a).1*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have HH:=(H a haN).1 [.diag d] (by simp only [List.length_singleton];omega) (hword d hd')
    simpa [matrixWord,matrixLetter,t₀,a₀,SmallTree.tree] using HH
  have herrorF : (∑i,|D.startedFieldError w y T t₀.tree a₀ x a i i|)≤
      (errorBudget R (fun a=>if a=0 then C+F else Cs a)
        (fun a=>if a=0 then |I.j*siteMean I.implicitCoefficient x| *(C+F)+F else Cf a) a).2*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have HH:=(H a haN).2 [.diag d] (by simp only [List.length_singleton];omega) (hword d hd')
    simpa [matrixWord,matrixLetter,t₀,a₀,SmallTree.tree] using HH
  have hadd (Q R : Interaction n) : (∑i,|Q i i|)≤(∑i,|R i i|)+(∑i,|(Q-R) i i|) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [Matrix.sub_apply,add_sub_cancel] using abs_add_le (R i i) (Q i i-R i i)
  exact ⟨(hadd _ _).trans (add_le_add hret.1 herrorS),(hadd _ _).trans (add_le_add hret.2 herrorF)⟩

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open Matrix Primary Primary.Tensor.Series
variable {n : ℕ}
open Marked

def pairBudget (V : Pair n) : ℝ := V.1.budget+V.2.budget
lemma pairBudget_nonneg (V : Pair n) : 0≤pairBudget V := add_nonneg (budget_nonneg _) (budget_nonneg _)
lemma mass_nonneg (P : GradedWords (Fin n)) : 0≤Marked.mass P := by
  unfold Marked.mass
  exact List.sum_nonneg (by intro r hr; obtain ⟨t,_,rfl⟩:=List.mem_map.mp hr;exact abs_nonneg _)
lemma smallBranch_budget (j : ℝ) (p : Fin n→ℝ) (T : GradedWords (Fin n)×GradedWords (Fin n)) (V : Pair n) :
    pairBudget (smallBranch j p T V)=
      SKGapCutoff.Recipe.vectorNorm p*(2*Marked.mass T.2+|j| *Marked.mass T.1)+pairBudget V := by
  simp only [pairBudget,smallBranch,budget_append,budget_prefix,budget_diagonalWords,budget_averageWords,abs_neg]
  ring
lemma boundedBranch_budget (j : ℝ) (p : Fin n→ℝ) (U V : Pair n) {A : ℝ}
    (hp : |Diagram.mean p|≤A) :
    pairBudget (boundedBranch j p U V)≤(2+|j| *A)*pairBudget U+pairBudget V := by
  simp only [pairBudget,boundedBranch,budget_append,budget_prefix,budget_scale,abs_neg,abs_mul]
  have H:=mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg j) (budget_nonneg U.1))
  nlinarith [budget_nonneg U.1,budget_nonneg U.2,
    mul_nonneg (mul_nonneg (abs_nonneg j) (le_trans (abs_nonneg _) hp)) (budget_nonneg U.2)]
lemma implicitPair_pairBudget (j : ℝ) (a p : Fin n→ℝ) (t : SourceTree (Fin n→ℝ)) :
    pairBudget (implicitPair j a p t)=
      (2+|j*Diagram.mean a|)*(SKGapCutoff.Recipe.vectorNorm p*
        (Marked.mass (GradedWords.ordinaryWords j t).2+|j| *Marked.mass (GradedWords.ordinaryWords j t).1))+
        |j| *SKGapCutoff.Recipe.vectorNorm p*Marked.mass (GradedWords.ordinaryWords j t).1 := by
  simp only [pairBudget,implicitPair,budget_append,budget_prefix,budget_scale,budget_diagonalWords,budget_averageWords,abs_neg]
  ring
lemma implicitPair_budget_le (j : ℝ) (a p : Fin n→ℝ) (t : SourceTree (Fin n→ℝ))
    {A B Q : ℝ} (hp : SKGapCutoff.Recipe.vectorNorm p≤B) (hQ : 0≤Q)
    (hq : Marked.mass (GradedWords.ordinaryWords j t).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords j t).2≤Q)
    (ha : |Diagram.mean a|≤A) :
    pairBudget (implicitPair j a p t)≤(2+|j| *A)*(B*((1+|j|)*Q))+|j| *B*Q := by
  rw [implicitPair_pairBudget,abs_mul]
  have hB:0≤B:=(SKGapCutoff.Recipe.vectorNorm_nonneg _).trans hp
  have hA:0≤A:=(abs_nonneg _).trans ha
  apply add_le_add
  · apply mul_le_mul
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
    · apply le_trans (mul_le_mul_of_nonneg_left (show _ ≤ (1+|j|)*Q from ?_) (SKGapCutoff.Recipe.vectorNorm_nonneg p))
      · exact mul_le_mul_of_nonneg_right hp (mul_nonneg (by positivity) hQ)
      · nlinarith [mul_le_mul_of_nonneg_left hq.1 (abs_nonneg j),hq.2]
    · positivity [SKGapCutoff.Recipe.vectorNorm_nonneg p,mass_nonneg (GradedWords.ordinaryWords j t).1,mass_nonneg (GradedWords.ordinaryWords j t).2]
    · positivity
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hp (abs_nonneg _)) hq.1 (mass_nonneg _) (mul_nonneg (abs_nonneg _) hB)

namespace SmallTree
lemma smallBranches_budget (j : ℝ) (a₀ : Fin n→ℝ)
    (xs : List ((Fin n→ℝ)×ClosedTree (Fin n→ℝ))) (U : SmallTree n) :
    pairBudget ((smallBranches xs U).marked j a₀)=
      (xs.map (fun t=>SKGapCutoff.Recipe.vectorNorm t.1*(2*Marked.mass (t.2.words j a₀).2+
        |j| *Marked.mass (t.2.words j a₀).1))).sum+pairBudget (U.marked j a₀) := by
  induction xs with
  | nil => simp [smallBranches]
  | cons t xs ih =>
    simp only [smallBranches,List.foldr_cons,marked,smallBranch_budget,List.map_cons,List.sum_cons] at *
    rw [ih];ring
lemma boundedBranches_budget (j : ℝ) (a₀ : Fin n→ℝ)
    (xs : List ((Fin n→ℝ)×SmallTree n)) (U : SmallTree n) {A : ℝ}
    (ha : ∀t∈xs,|Diagram.mean t.1|≤A) :
    pairBudget ((boundedBranches xs U).marked j a₀)≤
      (xs.map (fun t=>(2+|j| *A)*pairBudget (t.2.marked j a₀))).sum+pairBudget (U.marked j a₀) := by
  induction xs with
  | nil => simp [boundedBranches]
  | cons t xs ih =>
    simp only [boundedBranches,List.foldr_cons,marked,List.map_cons,List.sum_cons]
    exact (boundedBranch_budget j _ _ _ (ha t (by simp))).trans
      (by simpa only [add_assoc,boundedBranches] using add_le_add (le_refl ((2+|j| *A)*pairBudget (t.2.marked j a₀))) (ih (fun v hv=>ha v (by simp [hv]))))
end SmallTree
end SKGap.Noncrossing.ClosedMarked

end
end

end OAI
