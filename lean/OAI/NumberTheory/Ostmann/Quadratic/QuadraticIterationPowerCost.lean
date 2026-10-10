import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDescentCutoff
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicCount

namespace OAI

/-! # The explicit small-power cost of a fixed number of descent steps -/

namespace Ostmann

theorem quadratic_iteration_power_cost {η C : ℝ} (hη : 0 < η) (hC : 0 < C)
    {M N r : ℕ} (hM : 0 < M) (hN : 0 < N) (hr : 0 < r) :
    (r : ℝ) * (C * (Nat.log 2 N + 1 : ℕ) * (2 * (N : ℝ)) ^ η) ^ r *
        (C * (Nat.log 2 N + 1 : ℕ) * ((M : ℝ) * N) ^ (36 * η) *
          (quadraticDescentCutoff N r : ℝ) ^ 5) ≤
      ((r : ℝ) * (C * (1 + (η * Real.log 2)⁻¹) * 2 ^ η) ^ r *
        (C * (1 + (η * Real.log 2)⁻¹) * 5 ^ 5)) *
        ((M : ℝ) * N) ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ)) := by
  let X := (M : ℝ) * N
  let A := 1 + (η * Real.log 2)⁻¹
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hNX : (N : ℝ) ≤ X := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp [X]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hp : (N : ℝ) ^ η ≤ X ^ η := Real.rpow_le_rpow (Nat.cast_nonneg _) hNX hη.le
  have hl : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ A * X ^ η :=
    (quadratic_dyadic_count_bound η hη N hN).trans (mul_le_mul_of_nonneg_left hp hA.le)
  have htwo : (2 * (N : ℝ)) ^ η ≤ 2 ^ η * X ^ η := by
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hroot : (quadraticDescentCutoff N r : ℝ) ^ 5 ≤ 5 ^ 5 * X ^ (5 / (r : ℝ)) :=
    (quadratic_descent_cutoff_fifth hN hr).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hNX (by positivity)) (by positivity))
  have hfirst : C * (Nat.log 2 N + 1 : ℕ) * (2 * (N : ℝ)) ^ η ≤
      (C * A * 2 ^ η) * X ^ (2 * η) := by
    calc
      _ ≤ C * (A * X ^ η) * (2 ^ η * X ^ η) := by gcongr
      _ = _ := by
        rw [show 2 * η = η + η by ring, Real.rpow_add hX]
        ring
  have hsecond : C * (Nat.log 2 N + 1 : ℕ) * X ^ (36 * η) *
      (quadraticDescentCutoff N r : ℝ) ^ 5 ≤
      (C * A * 5 ^ 5) * X ^ (37 * η + 5 / (r : ℝ)) := by
    calc
      _ ≤ C * (A * X ^ η) * X ^ (36 * η) * (5 ^ 5 * X ^ (5 / (r : ℝ))) := by gcongr
      _ = _ := by
        rw [show 37 * η + 5 / (r : ℝ) = (η + 36 * η) + 5 / (r : ℝ) by ring,
          Real.rpow_add hX, Real.rpow_add hX]
        ring
  calc
    _ ≤ (r : ℝ) * ((C * A * 2 ^ η) * X ^ (2 * η)) ^ r *
        ((C * A * 5 ^ 5) * X ^ (37 * η + 5 / (r : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hfirst r) (Nat.cast_nonneg r)
      · exact hsecond
      · positivity
      · positivity
    _ = _ := by
      rw [mul_pow]
      rw [← Real.rpow_natCast (X ^ (2 * η)) r, ← Real.rpow_mul hX.le]
      have he : X ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ)) =
          X ^ ((2 * η) * r) * X ^ (37 * η + 5 / (r : ℝ)) := by
        rw [← Real.rpow_add hX]
        congr 1
        ring
      change _ = ((r : ℝ) * (C * A * 2 ^ η) ^ r * (C * A * 5 ^ 5)) *
        X ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ))
      rw [he]
      ring

end Ostmann

end OAI
