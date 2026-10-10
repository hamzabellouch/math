import OAI.Analysis.AllenCahn.DefectCalculus

namespace OAI

noncomputable section
namespace DeGiorgi
open MeasureTheory
open scoped ENNReal
open Filter Topology
open scoped ContDiff

lemma diffuseDefect_drift_inequality {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hAC : AllenCahn v) (x : Space n) :
    Laplacian.laplacian (diffuseDefect v) x ≤ 2 * diffuseDefect v x +
      fderiv ℝ (diffuseDefect v) x ((2 * Real.sqrt 2 * v x) • gradient (inverseProfile v) x) := by
  have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hp := inverseProfile_gradient_bound (smooth_C2 hv) hi hAC x
  have hpn := norm_nonneg (gradient (inverseProfile v) x)
  have hp2 : ‖gradient (inverseProfile v) x‖ ^ 2 ≤ 1 := by nlinarith
  have hq : defectWeight v x ≤ 1 := by dsimp [defectWeight]; nlinarith [sq_nonneg (v x)]
  have hq0 : 0 ≤ defectWeight v x := (weight_pos (hi x)).le
  have hh : 0 ≤ ∑ i : Fin n, ‖gradient (coordDeriv (inverseProfile v) i) x‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hprod : defectWeight v x * ‖gradient (inverseProfile v) x‖ ^ 2 ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hq hp2 (sq_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have H := mul_le_mul_of_nonneg_right hprod hD
  rw [diffuseDefect_laplacian hv hi hAC, map_smul, smul_eq_mul, ← inner_gradient_left]
  rw [real_inner_comm (gradient (diffuseDefect v) x)]
  nlinarith

end DeGiorgi
end

end OAI
