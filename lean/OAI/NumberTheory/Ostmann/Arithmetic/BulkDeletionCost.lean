import OAI.NumberTheory.Ostmann.Construction.PrimeRestorationDifference
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # Deleted-atom costs in the actual original bulk prior -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_deleted_reciprocal_mass_le (S D : Finset ℕ) (T : ℝ)
    (hlow : ∀ q ∈ S, Real.exp T ≤ (q : ℝ)) :
    (∑ q ∈ S ∩ D, (q : ℝ)⁻¹) ≤ (D.card : ℝ) * Real.exp (-T) := by
  calc
    _ ≤ ∑ _q ∈ S ∩ D, Real.exp (-T) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos T)
        (hlow q (Finset.mem_inter.mp hq).1)
    _ = ((S ∩ D).card : ℝ) * Real.exp (-T) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
      (Real.exp_nonneg _)

/-- All deleted values are charged using the old normalizers. If their
total mass is at most one, the product excess is at most twice that mass. -/
theorem bulk_deleted_product_cost {J : Type*} [Fintype J]
    (S D : J → Finset ℕ) (Z : J → ℝ) (H T K : ℝ)
    (hZ0 : ∀ j, 0 ≤ Z j) (hZ : ∀ j, Z j ≤ Real.exp H)
    (hcard : ∀ j, (D j).card ≤ K)
    (hlow : ∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ))
    (hsmall : (Fintype.card J : ℝ) * K * Real.exp (H - T) ≤ 1) :
    (∏ j, (1 + Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1 ≤
      2 * (Fintype.card J : ℝ) * K * Real.exp (H - T) := by
  let x := fun j => Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹
  have hx0 (j) : 0 ≤ x j := mul_nonneg (hZ0 j) (Finset.sum_nonneg fun _ _ => by positivity)
  have hx (j) : x j ≤ K * Real.exp (H - T) := by
    have hm := bulk_deleted_reciprocal_mass_le (S j) (D j) T (hlow j)
    have hk : 0 ≤ K := (Nat.cast_nonneg _).trans (hcard j)
    calc
      _ ≤ Real.exp H * ((D j).card * Real.exp (-T)) :=
        mul_le_mul (hZ j) hm (Finset.sum_nonneg fun _ _ => by positivity) (Real.exp_nonneg _)
      _ ≤ Real.exp H * (K * Real.exp (-T)) := by gcongr; exact hcard j
      _ = K * Real.exp (H - T) := by rw [Real.exp_sub, Real.exp_neg]; ring
  have hs0 : 0 ≤ ∑ j, x j := Finset.sum_nonneg fun j _ => hx0 j
  have hs : (∑ j, x j) ≤ (Fintype.card J : ℝ) * K * Real.exp (H - T) := by
    calc
      _ ≤ ∑ _j : J, K * Real.exp (H - T) := Finset.sum_le_sum fun j _ => hx j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have he := Real.abs_exp_sub_one_le (show |∑ j, x j| ≤ 1 by
    rw [abs_of_nonneg hs0]; exact hs.trans hsmall)
  have hp := Real.prod_one_add_le_exp_sum Finset.univ hx0
  change (∏ j, (1 + x j)) - 1 ≤ _
  have he' : Real.exp (∑ j, x j) - 1 ≤ 2 * ∑ j, x j := by
    rw [abs_of_nonneg hs0] at he
    exact (le_abs_self _).trans he
  linarith

end Ostmann

end OAI
