import Mathlib
import OAI.Probability.SKGap.Stability.StableFields
import OAI.Probability.SKGap.Localization.RecipeMarked

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

def pairBudget (V : Pair n) : ℝ := V.1.budget+V.2.budget

lemma budget_nonneg (P : MarkedPolynomial n) : 0≤P.budget := by
  unfold budget
  exact List.sum_nonneg (by intro r hr; obtain ⟨t,_,rfl⟩:=List.mem_map.mp hr; exact mul_nonneg (abs_nonneg _) (SKGapCutoff.Recipe.vectorNorm_nonneg _))
lemma pairBudget_nonneg (V : Pair n) : 0≤pairBudget V := add_nonneg (budget_nonneg _) (budget_nonneg _)
lemma mass_nonneg (P : WordPolynomial (ι:=Fin n)) : 0 ≤ mass P := by
  unfold mass
  exact List.sum_nonneg (by intro r hr; obtain ⟨t,_,rfl⟩:=List.mem_map.mp hr; exact abs_nonneg _)

lemma smallBranch_budget (j : ℝ) (p : Fin n→ℝ) (T : SourceTree (Fin n→ℝ)) (V : Pair n) :
    pairBudget (smallBranch j p T V)=
      SKGapCutoff.Recipe.vectorNorm p*(2*mass (T.words j).2+|j| *mass (T.words j).1)+pairBudget V := by
  simp only [pairBudget,smallBranch,budget_append,budget_prefix,budget_diagonalWords,budget_averageWords,abs_neg]
  ring
lemma boundedBranch_budget (j : ℝ) (p : Fin n→ℝ) (U V : Pair n) {A : ℝ}
    (hp : |Diagram.mean p|≤A) :
    pairBudget (boundedBranch j p U V) ≤ (2+|j| *A)*pairBudget U+pairBudget V := by
  simp only [pairBudget,boundedBranch,budget_append,budget_prefix,budget_scale,abs_neg,abs_mul]
  have h:=mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg j) (budget_nonneg U.1))
  nlinarith [budget_nonneg U.1,budget_nonneg U.2,
    mul_nonneg (mul_nonneg (abs_nonneg j) (le_trans (abs_nonneg _) hp)) (budget_nonneg U.2)]

lemma fold_budget {α : Type*} (xs : List α) (step : α→Pair n→Pair n) (cost : α→ℝ)
    (hstep : ∀a V,pairBudget (step a V)≤cost a+pairBudget V) :
    pairBudget (xs.foldr step zeroPair)≤(xs.map cost).sum := by
  induction xs with
  | nil => simp [zeroPair,pairBudget,budget,SmallMark.vector]
  | cons a xs ih =>
    exact (hstep a _).trans (by simpa only [List.map_cons,List.sum_cons] using add_le_add (le_refl (cost a)) ih)

end SKGap.Noncrossing.Primary.MarkedPolynomial
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing.Primary MarkedPolynomial
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def traceBudget (c k : ℝ) (W : ℕ→ℝ) (a : ℕ) : ℝ := c*W a+k*∑b:Fin a,traceBudget c k W b
termination_by a

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)
theorem markedRecipe_budget (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (N : ℕ)
    (W : ℕ→ℝ) {A M : ℝ} (hA : 0≤A) (hM : 0≤M)
    (hp : ∀a≤N,∀l,vectorNorm (D.sourcePartial a l x)≤W a)
    (hm : ∀l,mass ((T l).words D.j).1≤M ∧ mass ((T l).words D.j).2≤M)
    (ha : ∀a≤N,∀b:Fin a,|siteMean (D.auxCoefficient a b) x|≤A) :
    ∀a≤N,pairBudget (D.markedRecipe T x a)≤
      traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*M)) (2+|D.j| *A) W a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    rw [markedRecipe]
    let L : ℝ := (2+|D.j|)*M
    let K : ℝ := 2+|D.j| *A
    have hL : 0≤L := by dsimp [L]; positivity
    have hK : 0≤K := by dsimp [K]; positivity
    have H:=fold_budget (Finset.univ.toList.map (Sum.inl : ι→ι⊕Fin a)++Finset.univ.toList.map Sum.inr)
      (fun e V=>match e with
        | .inl l=>smallBranch D.j (D.sourcePartial a l x) (T l) V
        | .inr b=>boundedBranch D.j (D.auxCoefficient a b x) (D.markedRecipe T x b) V)
      (Sum.elim (fun _ : ι=>L*W a) (fun b:Fin a=>K*pairBudget (D.markedRecipe T x b)))
      (by
        intro e V
        cases e with
        | inl l=>
          rw [smallBranch_budget]
          apply add_le_add _ le_rfl
          have hc : 2*mass ((T l).words D.j).2+|D.j| *mass ((T l).words D.j).1≤L := by
            dsimp [L]
            nlinarith [(hm l).2,mul_le_mul_of_nonneg_left (hm l).1 (abs_nonneg D.j)]
          exact (mul_le_mul_of_nonneg_left hc (vectorNorm_nonneg _)).trans
            (by simpa [mul_comm] using mul_le_mul_of_nonneg_right (hp a haN l) hL)
        | inr b=>
          exact boundedBranch_budget D.j _ _ _ (by simpa only [siteMean,SKGap.Noncrossing.Diagram.mean,Fintype.card_fin] using ha a haN b))
    have hs : (∑b:Fin a,pairBudget (D.markedRecipe T x b))≤
        ∑b:Fin a,traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*M)) K W b := by
      apply Finset.sum_le_sum; intro b _; exact ih b b.isLt (b.isLt.le.trans haN)
    apply H.trans
    simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
    rw [traceBudget]
    have he : (List.map (fun b:Fin a=>K*pairBudget (D.markedRecipe T x b)) Finset.univ.toList).sum=
        K*∑b:Fin a,pairBudget (D.markedRecipe T x b) := by simp [Finset.mul_sum]
    have he0 : (List.map (fun _ : ι=>L*W a) Finset.univ.toList).sum=(Fintype.card ι:ℝ)*(L*W a) := by simp
    rw [he,he0]
    convert! add_le_add (le_refl ((Fintype.card ι:ℝ)*L*W a)) (mul_le_mul_of_nonneg_left hs hK) using 1
    try dsimp [L,K]
    ring

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonal_abs_sum_of_tests (M : Matrix ι ι ℝ) {C : ℝ}
    (h : ∀d:ι→ℝ,(∀i,|d i|≤1)→|trace (Matrix.diagonal d*M)|≤C) :
    (∑i,|M i i|)≤C := by
  let d : ι→ℝ := fun i=>if 0≤M i i then 1 else -1
  have hd : ∀i,|d i|≤1 := by intro i; dsimp [d]; split_ifs <;> norm_num
  have ht : trace (Matrix.diagonal d*M)=∑i,|M i i| := by
    simp only [trace,diag,Matrix.diagonal_mul]
    apply Finset.sum_congr rfl; intro i _
    dsimp [d]; split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  have H:=h d hd
  rw [ht,abs_of_nonneg (Finset.sum_nonneg fun i _=>abs_nonneg _)] at H
  exact H

end SKGap.Noncrossing
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram Matrix MarkedPolynomial
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem retainedSource_diagonal (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) (hn : 0<n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀t∈(D.markedRecipe T x a).1,
      SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) :
    (∑i,|D.retainedSource T x a i i|)≤(D.markedRecipe T x a).1.budget*B := by
  apply diagonal_abs_sum_of_tests
  intro d hd
  have H:=MarkedPolynomial.trace_error D.j D.J hn d hd (D.markedRecipe T x a).1 hB (hb d hd)
  have he : (D.markedRecipe T x a).1.plain=((D.retainedTree T x a).words D.j).1 :=
    congrArg Prod.fst (D.markedRecipe_plain T x a)
  rw [he] at H
  have hz : ∀i,polynomialPrediction D.j ((D.retainedTree T x a).words D.j).1 i=0 :=
    fun i=>(D.retained_prediction_zero T x a i).1
  simpa only [hz,mul_zero,Finset.sum_const_zero,sub_zero,retainedSource,SourceTree.sourceMatrix] using H

theorem retainedField_diagonal (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) (hn : 0<n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀t∈(D.markedRecipe T x a).2,
      SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) :
    (∑i,|D.retainedField T x a i i|)≤(D.markedRecipe T x a).2.budget*B := by
  apply diagonal_abs_sum_of_tests
  intro d hd
  have H:=MarkedPolynomial.trace_error D.j D.J hn d hd (D.markedRecipe T x a).2 hB (hb d hd)
  have he : (D.markedRecipe T x a).2.plain=((D.retainedTree T x a).words D.j).2 :=
    congrArg Prod.snd (D.markedRecipe_plain T x a)
  rw [he] at H
  have hz : ∀i,polynomialPrediction D.j ((D.retainedTree T x a).words D.j).2 i=0 :=
    fun i=>(D.retained_prediction_zero T x a i).2
  simpa only [hz,mul_zero,Finset.sum_const_zero,sub_zero,retainedField,SourceTree.fieldMatrix] using H

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
