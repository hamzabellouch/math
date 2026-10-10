import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullRows
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicCount
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveGrowth

namespace OAI

/-! # Recovering the full matrix bound from uniform dyadic estimates -/

namespace Ostmann

theorem quadratic_growth_of_dyadic (p : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      QuadraticRowBound ((oddSquarefreeRange (2 * M)).filter (M ≤ ·)) N
        (C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ p))) :
    QuadraticSieveGrowth p := by
  intro ε hε
  obtain ⟨C, hC, hc⟩ := h (ε / 2) (by positivity)
  let A := 1 + ((ε / 2) * Real.log 2)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2 * C * A, by positivity, ?_⟩
  intro M N hM hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hXp : 0 < (M : ℝ) * N := mul_pos hMR hNR
  have hMX : (M : ℝ) ≤ (M : ℝ) * N := le_mul_of_one_le_right hMR.le (by exact_mod_cast hN)
  have hl : ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ A * ((M : ℝ) * N) ^ (ε / 2) := by
    apply (quadratic_dyadic_count_bound (ε / 2) (by positivity) M hM).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hMR.le hMX (by positivity)) hA.le
  have hfull := quadratic_full_rows_of_dyadic (by positivity : (0 : ℝ) ≤ ε / 2)
    hC.le (by omega : 0 < M) (fun R hR => hc R N hR hN)
  apply (quadratic_sieve_of_row_bound hfull).mono_constant
  have he : ((M : ℝ) * N) ^ ε =
      ((M : ℝ) * N) ^ (ε / 2) * ((M : ℝ) * N) ^ (ε / 2) := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  calc
    _ ≤ 2 * ((A * ((M : ℝ) * N) ^ (ε / 2)) * C *
        ((M : ℝ) * N) ^ (ε / 2) * ((M : ℝ) + (N : ℝ) ^ p)) := by gcongr
    _ = _ := by rw [he]; ring

end Ostmann

end OAI
