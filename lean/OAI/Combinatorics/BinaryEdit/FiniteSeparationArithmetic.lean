import Mathlib

namespace OAI

/-!
# Deficit charges in the finite-tree separation induction

The exact deficit charges are those of `prop:finite-separation`.
-/

namespace TreeEdit.BinaryLower.FiniteTree

/-- At least half the children each charge `q` unmatched symbols. -/
theorem row_deficit_charge {m : ℕ} (bad : Finset (Fin m))
    (δ : Fin m → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hnonneg : ∀ i, 0 ≤ δ i) (hbad : ∀ i ∈ bad, q ≤ δ i)
    (hhalf : m ≤ 2 * bad.card) :
    (m : ℝ) * q / 2 ≤ ∑ i, δ i := by
  classical
  have hpoint (i : Fin m) : (if i ∈ bad then q else 0) ≤ δ i := by
    split_ifs with hi
    · exact hbad i hi
    · exact hnonneg i
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hcalc : (∑ i : Fin m, if i ∈ bad then q else 0) = (bad.card : ℝ) * q := by
    simp
  rw [hcalc] at hsum
  have hmR : (m : ℝ) ≤ 2 * (bad.card : ℝ) := by exact_mod_cast hhalf
  nlinarith [mul_le_mul_of_nonneg_right hmR hq]

/-- The chosen row charge is no larger than the tagged transition gap. -/
theorem finite_charge_le_gap (m h : ℕ) (hm : 2 ≤ m) (B : ℝ) (hB : 0 ≤ B) :
    (m : ℝ) * (B / (4 : ℝ) ^ h) / 2 ≤ ((m : ℝ) - 1) * B := by
  have hp : (1 : ℝ) ≤ (4 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  have hp0 : 0 < (4 : ℝ) ^ h := by positivity
  have hq : B / (4 : ℝ) ^ h ≤ B := by
    apply (div_le_iff₀ hp0).2
    nlinarith
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hq hm0]

/-- Half the total row charge is exactly the next `4⁻ʰ` separation scale. -/
theorem finite_charge_identity (m T h : ℕ) (B : ℝ) :
    (T : ℝ) * ((m : ℝ) * (B / (4 : ℝ) ^ h) / 2) / 2 =
      ((m : ℝ) * T * B) / (4 : ℝ) ^ (h + 1) := by
  rw [pow_succ]
  ring

end TreeEdit.BinaryLower.FiniteTree

end OAI
