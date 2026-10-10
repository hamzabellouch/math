import OAI.Geometry.RCD.Heat.FiniteHeatMassShells
import OAI.Geometry.RCD.Heat.GaussianShellKernel

namespace OAI

/-! # Local volume integration of Gaussian source bounds -/

open Set Metric MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- The local Gaussian volume sum has finite total mass in every fixed
dimension. It will control bounded-density curvature sources. -/
def gaussianVolumeMomentConstant (n : ℕ) (c : ℝ) : ℝ :=
  ∑' j : ℕ, ((2 : ℝ) ^ n) ^ j * gaussianShellFactor c j

theorem gaussianVolumeMomentConstant_nonneg (n : ℕ) (c : ℝ) :
    0 ≤ gaussianVolumeMomentConstant n c :=
  tsum_nonneg fun j => mul_nonneg (by positivity) (gaussianShellFactor_nonneg c j)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Integrating a supported Gaussian only needs upper ball volumes at
the finitely many scales inside its support. -/
theorem integral_gaussian_shell_le_volume (ν : Measure X) [IsFiniteMeasure ν]
    (n : ℕ) (x : X) {s C c V : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hc : 0 < c) (hV : 0 ≤ V)
    (N : ℕ) {f : X → ℝ} (hf : Integrable f ν)
    (hlocal : ∀ j ≤ N, ∀ z ∈ dyadicShell x s j,
      f z ≤ C / s ^ n * gaussianShellFactor c j)
    (hzero : ∀ z ∉ ball x (2 ^ N * s), f z = 0)
    (hvolume : ∀ j ≤ N, ν.real (ball x (2 ^ j * s)) ≤ V * (2 ^ j * s) ^ n) :
    (∫ z, f z ∂ν) ≤ C * V * gaussianVolumeMomentConstant n c := by
  have hb := integral_le_finite_shell_mass ν x hs.le N hf
    (fun j => C / s ^ n * gaussianShellFactor c j)
    (fun j => mul_nonneg (div_nonneg hC (pow_pos hs n).le) (gaussianShellFactor_nonneg c j))
    (fun j hj => by
      filter_upwards [ae_restrict_mem (measurableSet_dyadicShell x s j)] with z hz
      exact hlocal j hj z hz)
    (le_refl (0 : ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
      rw [hzero z hz])
  simp only [zero_mul, add_zero] at hb
  have hsum : (∑ j ∈ Finset.range (N + 1), (C / s ^ n * gaussianShellFactor c j) *
      ν.real (ball x (2 ^ j * s))) ≤
      C * V * ∑ j ∈ Finset.range (N + 1), ((2 : ℝ) ^ n) ^ j * gaussianShellFactor c j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      _ ≤ (C / s ^ n * gaussianShellFactor c j) * (V * (2 ^ j * s) ^ n) :=
        mul_le_mul_of_nonneg_left (hvolume j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
          (mul_nonneg (div_nonneg hC (pow_pos hs n).le) (gaussianShellFactor_nonneg c j))
      _ = _ := by rw [mul_pow, pow_right_comm (2 : ℝ) j n]; field_simp
  have hfinite : (∑ j ∈ Finset.range (N + 1), ((2 : ℝ) ^ n) ^ j * gaussianShellFactor c j) ≤
      gaussianVolumeMomentConstant n c :=
    (summable_gaussianShellFactor (show 0 ≤ (2 : ℝ) ^ n by positivity) hc).sum_le_tsum _
      (fun j _ => mul_nonneg (by positivity) (gaussianShellFactor_nonneg c j))
  exact hb.trans (hsum.trans (mul_le_mul_of_nonneg_left hfinite (mul_nonneg hC hV)))

end RegularPointCoordinates

end

end OAI
