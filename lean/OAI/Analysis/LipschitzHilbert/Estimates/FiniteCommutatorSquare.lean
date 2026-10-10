import OAI.Analysis.LipschitzHilbert.Estimates.FiniteSignedEnergy
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

/-! Uniform signed-multiplier commutator bounds imply square-function
control. This is the finite randomization step in frequency reassembly. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def finiteSignedOperator {n : ℕ} (P : Fin n → E →L[ℂ] E) (s : Fin n → Bool) : E →L[ℂ] E :=
  ∑ i, if s i then P i else -P i

theorem finiteSignedOperator_apply {n : ℕ} (P : Fin n → E →L[ℂ] E)
    (s : Fin n → Bool) (f : E) :
    finiteSignedOperator P s f=finiteSignedSum (fun i => P i f) s := by
  simp only [finiteSignedOperator,finiteSignedSum,sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem signed_commutator_apply {n : ℕ} (P : Fin n → E →L[ℂ] E)
    (T : E →L[ℂ] E) (s : Fin n → Bool) (f : E) :
    finiteSignedSum (fun i => P i (T f)-T (P i f)) s=
      finiteSignedOperator P s (T f)-T (finiteSignedOperator P s f) := by
  rw [finiteSignedOperator_apply,finiteSignedOperator_apply]
  simp only [finiteSignedSum,map_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [sub_eq_add_neg,add_comm]

theorem finite_commutator_square_bound {n : ℕ} (P : Fin n → E →L[ℂ] E)
    (T : E →L[ℂ] E) (A : ℝ) (f : E)
    (hbound : ∀ s : Fin n → Bool,
      ‖finiteSignedOperator P s (T f)-T (finiteSignedOperator P s f)‖≤A*‖f‖) :
    (∑ i, ‖P i (T f)-T (P i f)‖^2)≤A^2*‖f‖^2 := by
  apply finiteSignedSum_square_le
  intro s
  rw [signed_commutator_apply]
  exact (pow_le_pow_left₀ (norm_nonneg _) (hbound s) 2).trans_eq (by ring)

theorem finite_reassembly_square_bound {n : ℕ} (P : Fin n → E →L[ℂ] E)
    (T : E →L[ℂ] E) (A B N : ℝ) (_hB : 0≤B) (f : E)
    (hcomm : ∀ s : Fin n → Bool,
      ‖finiteSignedOperator P s (T f)-T (finiteSignedOperator P s f)‖≤A*‖f‖)
    (hband : ∀ i, ‖T (P i f)‖≤B*‖P i f‖)
    (hframe : (∑ i, ‖P i f‖^2)≤N*‖f‖^2) :
    (∑ i, ‖P i (T f)‖^2)≤2*(A^2+B^2*N)*‖f‖^2 := by
  have hc := finite_commutator_square_bound P T A f hcomm
  have hb : (∑ i, ‖T (P i f)‖^2)≤B^2*N*‖f‖^2 := by
    calc
      _ ≤ ∑ i, (B*‖P i f‖)^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hband i) 2)
      _ = B^2*(∑ i, ‖P i f‖^2) := by simp only [mul_pow,Finset.mul_sum]
      _ ≤ B^2*(N*‖f‖^2) := mul_le_mul_of_nonneg_left hframe (sq_nonneg B)
      _ = _ := by ring
  have hp (i : Fin n) : ‖P i (T f)‖^2≤
      2*‖P i (T f)-T (P i f)‖^2+2*‖T (P i f)‖^2 := by
    have hn := norm_add_le (P i (T f)-T (P i f)) (T (P i f))
    rw [sub_add_cancel] at hn
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖P i (T f)-T (P i f)‖-‖T (P i f)‖)]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hp i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  nlinarith

end LipschitzHilbert

end

end OAI
