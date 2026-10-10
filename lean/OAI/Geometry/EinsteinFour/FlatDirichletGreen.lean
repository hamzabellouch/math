import OAI.Geometry.EinsteinFour.ScalarDirichlet

namespace OAI

/-! The explicit positive Green kernel for the flat discrete Dirichlet operator. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

def flatGreenValue (N j i : ℕ) : ℝ :=
  (min i j : ℕ) - (i : ℝ) * j / (N + 1)

def flatGreen (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => flatGreenValue N (j.val + 1) (i.val + 1)

private theorem tent_second_difference (i j : ℕ) :
    2 * (min (i + 1) j : ℕ) - (min i j : ℕ) - (min (i + 2) j : ℕ) =
      (if i + 1 = j then (1 : ℝ) else 0) := by
  by_cases h : j ≤ i
  · have h1 : j ≤ i + 1 := by omega
    have h2 : j ≤ i + 2 := by omega
    have hn : i + 1 ≠ j := by omega
    simp only [min_eq_right h, min_eq_right h1, min_eq_right h2, ite_eq_right hn]
    ring
  · by_cases he : i + 1 = j
    · subst j
      simp only [min_eq_left (by omega : i ≤ i + 1), min_self,
        min_eq_right (by omega : i + 1 ≤ i + 2), ite_true, Nat.cast_add, Nat.cast_one]
      ring
    · have h2 : i + 2 ≤ j := by omega
      simp only [min_eq_left (by omega : i ≤ j), min_eq_left (by omega : i + 1 ≤ j),
        min_eq_left h2, ite_eq_right he, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      ring

theorem flatGreenValue_second_difference (N i j : ℕ) :
    2 * flatGreenValue N j (i + 1) - flatGreenValue N j i -
      flatGreenValue N j (i + 2) = if i + 1 = j then 1 else 0 := by
  have h := tent_second_difference i j
  simp only [flatGreenValue, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linear_combination h

theorem scalarDirichlet_mul_flatGreen (N : ℕ) : scalarDirichlet N 2 * flatGreen N = 1 := by
  ext i j
  have h0 : flatGreenValue N (j.val + 1) 0 = 0 := by simp [flatGreenValue]
  have hN : flatGreenValue N (j.val + 1) (N + 1) = 0 := by
    have hj : j.val + 1 ≤ N + 1 := by omega
    simp only [flatGreenValue, min_eq_right hj, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have h := scalarDirichlet_apply_sequence 2 (flatGreenValue N (j.val + 1)) h0 hN i
  change (scalarDirichlet N 2 *ᵥ fun k => flatGreenValue N (j.val + 1) (k.val + 1)) i = _
  rw [h, flatGreenValue_second_difference]
  by_cases hij : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
    simp [hv, hij]

theorem flatGreen_nonneg (N : ℕ) (i j : Fin N) : 0 ≤ flatGreen N i j := by
  have hd : (0 : ℝ) < N + 1 := by positivity
  have hi : (i.val : ℝ) + 1 ≤ N + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt i.isLt)
  have hj : (j.val : ℝ) + 1 ≤ N + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt j.isLt)
  change 0 ≤ flatGreenValue N (j.val + 1) (i.val + 1)
  unfold flatGreenValue
  by_cases hij : i.val ≤ j.val
  · rw [min_eq_left (by omega : i.val + 1 ≤ j.val + 1)]
    push_cast
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · rw [min_eq_right (by omega : j.val + 1 ≤ i.val + 1)]
    push_cast
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith

end
end PositiveEinsteinFour.Jacobi

end OAI
