import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SquarefreeExpression

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression
open Finset Classical
variable {ι : Type*} [DecidableEq ι] {E F : ℕ}

noncomputable def zeroExpression (ι : Type*) [DecidableEq ι] (E : ℕ) : SquarefreeExpression ι E where
  factors _ := ∅
  coefficient _ := 0

noncomputable def append (d : SquarefreeExpression ι E) (e : SquarefreeExpression ι F) :
    SquarefreeExpression ι (E+F) where
  factors := Fin.addCases d.factors e.factors
  coefficient := Fin.addCases d.coefficient e.coefficient

noncomputable def neg (d : SquarefreeExpression ι E) : SquarefreeExpression ι E where
  factors := d.factors
  coefficient i := -d.coefficient i

@[simp] lemma eval_zero (x : ι → ℤ) : (zeroExpression ι E).eval x=0 := by simp [eval,zeroExpression]
@[simp] lemma coefficient_zero (q : ι) (x : ι → ℤ) : (zeroExpression ι E).linearCoeff q x=0 := by
  simp [linearCoeff,zeroExpression]
@[simp] lemma support_zero : (zeroExpression ι E).support=∅ := by ext v; simp [support,zeroExpression]

@[simp] lemma eval_append (d : SquarefreeExpression ι E) (e : SquarefreeExpression ι F) (x : ι → ℤ) :
    (d.append e).eval x=d.eval x+e.eval x := by
  unfold eval
  rw [Fin.sum_univ_add]
  simp only [append,Fin.addCases_left,Fin.addCases_right]

@[simp] lemma coefficient_append (d : SquarefreeExpression ι E) (e : SquarefreeExpression ι F)
    (q : ι) (x : ι → ℤ) : (d.append e).linearCoeff q x=d.linearCoeff q x+e.linearCoeff q x := by
  unfold linearCoeff
  rw [Fin.sum_univ_add]
  simp only [append,Fin.addCases_left,Fin.addCases_right]

@[simp] lemma eval_neg (d : SquarefreeExpression ι E) (x : ι → ℤ) : d.neg.eval x= -d.eval x := by
  simp only [eval,neg,neg_mul,sum_neg_distrib]

@[simp] lemma coefficient_neg (d : SquarefreeExpression ι E) (q : ι) (x : ι → ℤ) :
    d.neg.linearCoeff q x= -d.linearCoeff q x := by
  unfold linearCoeff
  rw [←sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  simp only [neg,neg_mul]
  split_ifs <;> simp

@[simp] lemma support_neg (d : SquarefreeExpression ι E) : d.neg.support=d.support := by
  simp only [support,neg,neg_eq_zero]

@[simp] lemma support_append (d : SquarefreeExpression ι E) (e : SquarefreeExpression ι F) :
    (d.append e).support=d.support ∪ e.support := by
  ext v
  simp only [support,mem_biUnion,mem_univ,true_and,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    refine Fin.addCases ?_ ?_ i hi
    · intro j hj; exact Or.inl ⟨j,by simpa only [append,Fin.addCases_left] using hj⟩
    · intro j hj; exact Or.inr ⟨j,by simpa only [append,Fin.addCases_right] using hj⟩
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨i.castAdd F,by simpa only [append,Fin.addCases_left] using hi⟩
    · exact ⟨i.natAdd E,by simpa only [append,Fin.addCases_right] using hi⟩

lemma factors_append_le (d : SquarefreeExpression ι E) (e : SquarefreeExpression ι F) (J : ℕ)
    (hd : ∀ i, (d.factors i).card ≤ J) (he : ∀ i, (e.factors i).card ≤ J) :
    ∀ i, ((d.append e).factors i).card ≤ J := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j; simpa only [append,Fin.addCases_left] using hd j
  · intro j; simpa only [append,Fin.addCases_right] using he j

lemma abs_coefficient_append_le (d : SquarefreeExpression ι E) (e : SquarefreeExpression ι F) (H : ℝ)
    (hd : ∀ i, |(d.coefficient i:ℝ)| ≤ H) (he : ∀ i, |(e.coefficient i:ℝ)| ≤ H) :
    ∀ i, |((d.append e).coefficient i:ℝ)| ≤ H := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j; simpa only [append,Fin.addCases_left] using hd j
  · intro j; simpa only [append,Fin.addCases_right] using he j

end OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression

end

end OAI
