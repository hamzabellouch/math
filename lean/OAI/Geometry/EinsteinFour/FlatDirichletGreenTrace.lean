import OAI.Geometry.EinsteinFour.FlatDirichletGreen
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Trace and mesh limit of the flat Green matrix. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped Topology
noncomputable section

private theorem sum_nodes (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 1)) = (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_nodes_sq (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ 2) = (N : ℝ) * (N + 1) * (2 * N + 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem flatGreen_trace (N : ℕ) : (flatGreen N).trace = N * (N + 2) / 6 := by
  simp only [Matrix.trace, Matrix.diag_apply, flatGreen, flatGreenValue, min_self,
    Nat.cast_add, Nat.cast_one]
  change (∑ i : Fin N, (fun j : ℕ => ((j : ℝ) + 1) -
    ((j : ℝ) + 1) * ((j : ℝ) + 1) / (N + 1)) i.val) = _
  rw [← Finset.sum_range (fun j : ℕ => ((j : ℝ) + 1) -
    ((j : ℝ) + 1) * ((j : ℝ) + 1) / (N + 1))]
  simp only [Finset.sum_sub_distrib, ← pow_two, ← Finset.sum_div]
  rw [sum_nodes, sum_nodes_sq]
  field_simp
  ring

def scaledFlatGreen (t : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (t / (N + 1)) ^ 2 • flatGreen N

theorem scaledFlatGreen_trace (t : ℝ) (N : ℕ) :
    (scaledFlatGreen t N).trace = (t ^ 2 / 6) * (1 - (1 / ((N : ℝ) + 1)) ^ 2) := by
  rw [scaledFlatGreen, Matrix.trace_smul, smul_eq_mul, flatGreen_trace]
  field_simp
  ring

theorem scaledFlatGreen_trace_tendsto (t : ℝ) :
    Tendsto (fun N => (scaledFlatGreen t N).trace) atTop (𝓝 (t ^ 2 / 6)) := by
  simp_rw [scaledFlatGreen_trace]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub h).const_mul (t ^ 2 / 6)

theorem scaledFlatGreen_nonneg (t : ℝ) (N : ℕ) (i j : Fin N) :
    0 ≤ scaledFlatGreen t N i j :=
  mul_nonneg (sq_nonneg _) (flatGreen_nonneg N i j)

end
end PositiveEinsteinFour.Jacobi

end OAI
