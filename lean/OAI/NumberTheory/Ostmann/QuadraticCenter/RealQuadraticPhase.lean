import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! # Real quadratic phases and their linear correlations

These are the concrete exponential sums used in the inverse quadratic step.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def realAdditivePhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem realAdditivePhase_zero : realAdditivePhase 0 = 1 := by
  simp [realAdditivePhase]

@[simp] theorem norm_realAdditivePhase (x : ℝ) : ‖realAdditivePhase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem realAdditivePhase_add (x y : ℝ) :
    realAdditivePhase (x + y) = realAdditivePhase x * realAdditivePhase y := by
  unfold realAdditivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realAdditivePhase_nat_mul (n : ℕ) (x : ℝ) :
    realAdditivePhase ((n : ℝ) * x) = realAdditivePhase x ^ n := by
  unfold realAdditivePhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

@[simp] theorem conj_realAdditivePhase (x : ℝ) :
    conj (realAdditivePhase x) = realAdditivePhase (-x) := by
  unfold realAdditivePhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem realAdditivePhase_sub (x y : ℝ) :
    realAdditivePhase (x - y) = realAdditivePhase x * conj (realAdditivePhase y) := by
  rw [sub_eq_add_neg, realAdditivePhase_add, conj_realAdditivePhase]

noncomputable def realQuadraticPhase (α β : ℝ) (j : ℕ) : ℂ :=
  realAdditivePhase (α * (j : ℝ) ^ 2 + β * j)

theorem realQuadraticPhase_correlation (α β : ℝ) (h j : ℕ) :
    realQuadraticPhase α β (j + h) * conj (realQuadraticPhase α β j) =
      realAdditivePhase (α * (h : ℝ) ^ 2 + β * h) *
        realAdditivePhase (2 * α * h) ^ j := by
  unfold realQuadraticPhase
  rw [← realAdditivePhase_sub, ← realAdditivePhase_nat_mul, ← realAdditivePhase_add]
  congr 1
  push_cast
  ring

theorem norm_quadratic_correlation_sum (α β : ℝ) (h N : ℕ) :
    ‖∑ j ∈ Finset.range N,
      realQuadraticPhase α β (j + h) * conj (realQuadraticPhase α β j)‖ =
      ‖∑ j ∈ Finset.range N, realAdditivePhase (2 * α * h) ^ j‖ := by
  simp_rw [realQuadraticPhase_correlation, ← Finset.mul_sum, Complex.norm_mul,
    norm_realAdditivePhase, one_mul]

/-- The elementary geometric-sum bound, retaining the exact denominator. -/
theorem norm_geometric_sum_le (z : ℂ) (N : ℕ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ min (N : ℝ) (2 / ‖z - 1‖) := by
  apply le_min
  · calc
      _ ≤ ∑ j ∈ Finset.range N, ‖z ^ j‖ := norm_sum_le _ _
      _ = N := by norm_num [hz]
  · have heq := geom_sum_mul z N
    have hnorm : ‖∑ j ∈ Finset.range N, z ^ j‖ * ‖z - 1‖ = ‖z ^ N - 1‖ := by
      rw [← Complex.norm_mul, heq]
    have hb : ‖z ^ N - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by norm_num [hz]
    exact (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1))).mpr (hnorm.trans_le hb)

end Ostmann

end OAI
