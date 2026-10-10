import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleOrdinarySum

namespace OAI

/-! An exact partition of the remaining large tuples. A boundary box
retains its sharp distinguished-product cutoff; an exceptional high box
has no surviving ordinary tuple. No contribution is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleBoundarySum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if largeTupleDistinguishedScale (fun a => (d a).val) < X^(38/100:ℝ) ∧
      X^(38/100:ℝ) ≤ 2^i*largeTupleDistinguishedScale (fun a => (d a).val) then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

def largePrimeTupleExceptionalHighSum (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      ¬(∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q) then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

lemma largePrimeTuplePiece_low_zero (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H : ℝ)
    {X : ℝ} (hX : 0 < X)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hlow : 2^i*largeTupleDistinguishedScale (fun a => (d a).val) < X^(38/100:ℝ)) :
    largePrimeTuplePiece i j 0 ξ Ct H X d = 0 := by
  unfold largePrimeTuplePiece
  rw [Finset.sum_eq_zero (fun q hq => largePrimeTupleTerm_low_box 0 ξ Ct H hX d hlow hq),mul_zero]

theorem distinguishedPrimeTupleLow_residual_partition (i j : ℕ) (ξ δ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    distinguishedPrimeTupleLow i j 0 ξ Ct H X =
      largePrimeTupleOrdinaryHighSum i j ξ δ Ct H X +
      largePrimeTupleExceptionalHighSum i j ξ δ Ct H X +
      largePrimeTupleBoundarySum i j ξ Ct H X := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have henvelope : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le
      (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  rw [distinguishedPrimeTupleLow_partition i j 0 ξ Ct H henvelope]
  unfold largePrimeTupleOrdinaryHighSum largePrimeTupleExceptionalHighSum largePrimeTupleBoundarySum
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hhigh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
  · by_cases ho : ∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q
    · simp only [hhigh,ho,true_and,ite_true,not_true_eq_false,and_false,ite_false,
        not_lt_of_ge hhigh,false_and,add_zero]
    · simp only [hhigh,ho,true_and,ite_false,not_false_eq_true,ite_true,
        not_lt_of_ge hhigh,false_and,zero_add,add_zero]
  · by_cases hboundary : X^(38/100:ℝ) ≤ 2^i*largeTupleDistinguishedScale (fun a => (d a).val)
    · simp only [hhigh,false_and,ite_false,lt_of_not_ge hhigh,hboundary,and_self,ite_true,zero_add]
    · have hz := largePrimeTuplePiece_low_zero i j ξ Ct H hXp d (lt_of_not_ge hboundary)
      simp only [hhigh,false_and,ite_false,hboundary,and_false,zero_add,hz]

end CubicFirstMoment

end

end OAI
