import OAI.Geometry.RCD.Heat.FiniteHeatMassShells
import OAI.Geometry.RCD.Heat.GaussianMassEnvelope

namespace OAI

/-! # Gaussian integration against full finite source measures -/

open Set Metric MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The geometric shell bound applies to every integrable source weight,
including averaged kernels and differences of kernels. -/
theorem scaled_integral_le_geometric_mass (ν : Measure X) [IsFiniteMeasure ν]
    (m : ℕ) (p : X) {r C c T : ℝ} {f : X → ℝ}
    (hr : 0 < r) (hf : Integrable f ν) (hC : 0 ≤ C) (hc : 0 < c)
    (hT : 0 ≤ T) (N : ℕ)
    (hlocal : ∀ j ≤ N, ∀ z ∈ dyadicShell p r j,
      f z ≤ (C / r ^ (m + 2)) * gaussianShellFactor c j)
    (htail : ∀ z ∉ ball p (2 ^ N * r), f z ≤ T) :
    r ^ 2 * (∫ z, f z ∂ν) ≤
      C * gaussianMassConvolutionConstant m c *
        (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
          (((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) *
            ν.real (ball p (2 ^ j * r)))) + r ^ 2 * T * ν.real univ := by
  have hb := integral_le_finite_shell_mass ν p hr.le N hf
    (fun j => (C / r ^ (m + 2)) * gaussianShellFactor c j)
    (fun j => mul_nonneg (div_nonneg hC (pow_pos hr _).le) (gaussianShellFactor_nonneg c j))
    (by
      intro j hj
      filter_upwards [ae_restrict_mem (measurableSet_dyadicShell p r j)] with z hz
      exact hlocal j hj z hz) hT
    (by
      filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
      exact htail z hz)
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg r)
  rw [mul_add, Finset.mul_sum] at hm
  have hsum : (∑ j ∈ Finset.range (N + 1), r ^ 2 *
      ((C / r ^ (m + 2) * gaussianShellFactor c j) * ν.real (ball p (2 ^ j * r)))) ≤
      C * gaussianMassConvolutionConstant m c *
        (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
          (((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) *
            ν.real (ball p (2 ^ j * r)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    let mass := ((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) *
      ν.real (ball p (2 ^ j * r))
    have hmass : 0 ≤ mass := by dsimp only [mass]; positivity
    have hcoef := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (gaussian_mass_coefficient_le m hc j) hC) hmass
    calc
      _ = (C * (((2 : ℝ) ^ m) ^ j * gaussianShellFactor c j)) * mass := by
        have he := scaled_mass_dyadic_identity m j hr (ν.real (ball p (2 ^ j * r)))
        dsimp only [mass]
        calc
          _ = (C * gaussianShellFactor c j) *
              ((r ^ 2 / r ^ (m + 2)) * ν.real (ball p (2 ^ j * r))) := by ring
          _ = _ := by rw [he]; ring
      _ ≤ _ := by simpa only [mul_assoc] using hcoef
  nlinarith only [hm, hsum]

end RegularPointCoordinates

end

end OAI
