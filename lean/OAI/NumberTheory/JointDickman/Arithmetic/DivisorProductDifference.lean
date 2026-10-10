import OAI.NumberTheory.JointDickman.Arithmetic.DivisorProductMean

namespace OAI

/-! # Removing large-prime factors from a divisor product in mean -/
namespace JointDickman
open Finset Classical

theorem divisor_product_difference_mean {P Q : Finset ℕ} (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) (hb : ∀ p ∈ P, 0 ≤ b p) (U : ℕ) :
    (∑ n ∈ Ioc 0 U, ((∏ p ∈ P, if p ∣ n then 1+b p else 1)-
      ∏ p ∈ Q, if p ∣ n then 1+b p else 1)) ≤
      (U : ℝ)*((∏ p ∈ P, (1+b p/p))-(∏ p ∈ Q, (1+b p/p))) := by
  have hsets : Q.powerset ⊆ P.powerset := powerset_mono.mpr hQP
  simp_rw [divisor_product_expansion P hP b,
    divisor_product_expansion Q (fun p hp => hP p (hQP hp)) b,← sum_sdiff hsets,add_sub_cancel_right]
  rw [sum_comm]
  calc
    _ = ∑ D ∈ P.powerset \ Q.powerset,
        ((U/(∏ p ∈ D, p) : ℕ) : ℝ)*∏ p ∈ D, b p := by
      apply sum_congr rfl
      intro D _
      rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ D ∈ P.powerset \ Q.powerset,
        ((U : ℝ)/(∏ p ∈ D, p))*∏ p ∈ D, b p := by
      apply sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_right Nat.cast_div_le
      exact prod_nonneg (fun p hp => hb p (mem_powerset.mp (mem_sdiff.mp hD).1 hp))
    _ = (U : ℝ)*∑ D ∈ P.powerset \ Q.powerset, ∏ p ∈ D, b p/p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro D _
      rw [prod_div_distrib,Nat.cast_prod]
      ring
    _ = _ := by
      have hs := sum_sdiff hsets (f := fun D : Finset ℕ => ∏ p ∈ D, b p/p)
      rw [← prod_one_add,← prod_one_add] at hs
      congr 1
      linarith

end JointDickman

end OAI
