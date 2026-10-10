import OAI.NumberTheory.JointDickman.Counting.PeriodicNonnegative

namespace OAI

/-! # Sparse errors for a periodic nonnegative weight in a rectangle -/

namespace JointDickman

open Finset

/-- The rectangle error retains the mass in a single residue square,
which is essential when only a few residue lines are allowed. -/
theorem nonnegative_periodic_rectangle_error {q : ℕ} (hq : 0 < q)
    (F : ZMod q → ZMod q → ℝ) (hF : ∀ r s, 0 ≤ F r s)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        (((b : ℝ) - a) * ((d : ℝ) - c) / (q : ℝ) ^ 2) *
          ∑ r ∈ range q, ∑ s ∈ range q, F r s| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / q + 2) *
        ∑ r ∈ range q, ∑ s ∈ range q, F r s := by
  let G := fun r : ZMod q => ∑ s ∈ range q, F r s
  let M := ∑ r ∈ range q, G r
  let L₁ : ℝ := (b : ℝ) - a
  let L₂ : ℝ := (d : ℝ) - c
  have hL₁ : 0 ≤ L₁ := sub_nonneg.mpr (by exact_mod_cast hab)
  have hL₂ : 0 ≤ L₂ := sub_nonneg.mpr (by exact_mod_cast hcd)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hG (r : ZMod q) : 0 ≤ G r := sum_nonneg (fun s _ => hF r s)
  have hmass : 0 ≤ M := sum_nonneg (fun r _ => hG r)
  have hrow (m : ℕ) := nonnegative_periodic_interval_error hq (F m) (hF m) hcd
  have houter := nonnegative_periodic_interval_error hq G hG hab
  change |(∑ m ∈ Ico a b, G m) - L₁ / q * M| ≤ 2 * M at houter
  have hsumG : (∑ m ∈ Ico a b, G m) ≤ (L₁ / q + 2) * M := by
    linarith [(abs_le.mp houter).2]
  have hsumrow : |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
      L₂ / q * ∑ m ∈ Ico a b, G m| ≤ 2 * ∑ m ∈ Ico a b, G m := by
    rw [mul_sum, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ m ∈ Ico a b, 2 * G m := by
        apply sum_le_sum
        intro m _
        exact hrow m
      _ = _ := (mul_sum _ _ _).symm
  have hscaled : |L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| ≤
      L₂ / q * (2 * M) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hL₂ hq0.le)]
    exact mul_le_mul_of_nonneg_left houter (div_nonneg hL₂ hq0.le)
  change |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
    (L₁ * L₂ / (q : ℝ) ^ 2) * M| ≤ 2 * ((L₁ + L₂) / q + 2) * M
  calc
    _ = |((∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        L₂ / q * ∑ m ∈ Ico a b, G m) +
        L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        L₂ / q * ∑ m ∈ Ico a b, G m| +
        |L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| := abs_add_le _ _
    _ ≤ 2 * (∑ m ∈ Ico a b, G m) + L₂ / q * (2 * M) :=
      add_le_add hsumrow hscaled
    _ ≤ 2 * ((L₁ / q + 2) * M) + L₂ / q * (2 * M) := by linarith
    _ = _ := by ring

end JointDickman

end OAI
