import OAI.NumberTheory.JointDickman.Counting.TruncatedCoefficientVariation

namespace OAI

/-! # Uniform lag variation for a truncated row of the finite block -/
namespace JointDickman
open Finset Classical

theorem cutLagWeight_upper_variation (H U T : ℕ) (w : ℕ → ℝ) {A L : ℝ}
    (hT : 0 < T) (hU : 0 < U) (hUT : U ≤ T) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hw : ∀ j, H < j → j < U → |w j| ≤ A/(T : ℝ))
    (hd : ∀ j, H < j → j+1 < U → |w j-w (j+1)| ≤ L/(T : ℝ)^2) :
    finiteCoefficientVariation (cutLagWeight H U w) T ≤ (2*A+L)/T := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hstep (j : ℕ) :
      |cutLagWeight H U w j-cutLagWeight H U w (j+1)| ≤
        L/(T : ℝ)^2+(if j=H then A/(T : ℝ) else 0)+
          (if j+1=U then A/(T : ℝ) else 0) := by
    have hleft : 0 ≤ (if j=H then A/(T : ℝ) else 0) := by positivity
    have hright : 0 ≤ (if j+1=U then A/(T : ℝ) else 0) := by positivity
    have hder : 0 ≤ L/(T : ℝ)^2 := by positivity
    unfold cutLagWeight
    by_cases hj : H < j ∧ j < U <;> by_cases hj' : H < j+1 ∧ j+1 < U
    · rw [ite_eq_left hj,ite_eq_left hj']
      exact (hd j hj.1 hj'.2).trans (by linarith)
    · rw [ite_eq_left hj,ite_eq_right hj',sub_zero]
      have he : j+1=U := by omega
      rw [ite_eq_left he]
      exact (hw j hj.1 hj.2).trans (by linarith)
    · rw [ite_eq_right hj,ite_eq_left hj',zero_sub,abs_neg]
      have he : j=H := by omega
      rw [ite_eq_left he]
      exact (hw (j+1) hj'.1 hj'.2).trans (by linarith)
    · rw [ite_eq_right hj,ite_eq_right hj',sub_self,abs_zero]
      positivity
  have hsumH : (∑ j ∈ range T, if j=H then A/(T : ℝ) else 0) ≤ A/T := by
    rw [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hsumT : (∑ j ∈ range T, if j+1=U then A/(T : ℝ) else 0) ≤ A/T := by
    have he (j : ℕ) : j+1=U ↔ j=U-1 := by omega
    simp only [he,sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hsum := (sum_le_sum (fun j (_ : j ∈ range T) => hstep j)).trans
    (show (∑ j ∈ range T, (L/(T : ℝ)^2+(if j=H then A/(T : ℝ) else 0)+
      (if j+1=U then A/(T : ℝ) else 0))) ≤ (T : ℝ)*(L/(T : ℝ)^2)+A/T+A/T by
        rw [sum_add_distrib,sum_add_distrib,sum_const,card_range,nsmul_eq_mul]
        exact add_le_add (add_le_add le_rfl hsumH) hsumT)
  have h0 : cutLagWeight H U w 0 = 0 := by simp [cutLagWeight]
  have hTT : cutLagWeight H U w T = 0 := by simp [cutLagWeight,not_lt_of_ge hUT]
  rw [finiteCoefficientVariation,h0,hTT,abs_zero,zero_add,zero_add]
  apply hsum.trans_eq
  field_simp
  ring

end JointDickman

end OAI
