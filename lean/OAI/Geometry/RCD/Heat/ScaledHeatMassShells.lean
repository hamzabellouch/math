import OAI.Geometry.RCD.Heat.FiniteHeatMassShells
import OAI.Geometry.RCD.Heat.GaussianMassEnvelope

namespace OAI

/-! # Actual scaled heat mass is controlled by a geometric ball-mass convolution -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Gaussian shell bounds give the geometric convolution in the actual
ball masses, plus only the explicit exterior contribution. -/
theorem scaled_cutoffHeatMass_le_geometric (M : PositiveBilinearMeasure X E)
    (m : ℕ) (p : X) {r t C c T : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hC : 0 ≤ C) (hc : 0 < c) (hT : 0 ≤ T) (N : ℕ)
    (hlocal : ∀ j ≤ N, ∀ z ∈ dyadicShell p r j,
      χ z * ker t p z ≤ (C / r ^ (m + 2)) * gaussianShellFactor c j)
    (htail : ∀ z ∉ ball p (2 ^ N * r), χ z * ker t p z ≤ T) (v : E) :
    r ^ 2 * ⟪v, cutoffHeatMass μ hQ hk hχ hsχ M ht p v⟫_ℝ ≤
      C * gaussianMassConvolutionConstant m c *
        (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
          (((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) *
            (M.measure v).real (ball p (2 ^ j * r)))) +
      r ^ 2 * T * (M.measure v).real univ := by
  have hb := cutoffHeatMass_le_finite_shells μ hQ hk hχ hsχ M p hr.le ht N
    (fun j => (C / r ^ (m + 2)) * gaussianShellFactor c j)
    (fun j => mul_nonneg (div_nonneg hC (pow_pos hr _).le) (gaussianShellFactor_nonneg c j))
    hlocal hT htail v
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg r)
  rw [mul_add, Finset.mul_sum] at hm
  have hsum : (∑ j ∈ Finset.range (N + 1), r ^ 2 *
      ((C / r ^ (m + 2) * gaussianShellFactor c j) * (M.measure v).real (ball p (2 ^ j * r)))) ≤
      C * gaussianMassConvolutionConstant m c *
        (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
          (((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) *
            (M.measure v).real (ball p (2 ^ j * r)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    let mass := ((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) *
      (M.measure v).real (ball p (2 ^ j * r))
    have hmass : 0 ≤ mass := by dsimp only [mass]; positivity
    have hcoef := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (gaussian_mass_coefficient_le m hc j) hC) hmass
    calc
      _ = (C * (((2 : ℝ) ^ m) ^ j * gaussianShellFactor c j)) * mass := by
        have he := scaled_mass_dyadic_identity m j hr ((M.measure v).real (ball p (2 ^ j * r)))
        dsimp only [mass]
        calc
          _ = (C * gaussianShellFactor c j) *
              ((r ^ 2 / r ^ (m + 2)) * (M.measure v).real (ball p (2 ^ j * r))) := by ring
          _ = _ := by rw [he]; ring
      _ ≤ _ := by simpa only [mul_assoc] using hcoef
  nlinarith only [hm, hsum]

end RegularPointCoordinates

end

end OAI
