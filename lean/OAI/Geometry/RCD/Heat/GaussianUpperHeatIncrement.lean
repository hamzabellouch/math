import OAI.Geometry.RCD.Heat.HeatUpperIncrement
import OAI.Geometry.RCD.Heat.CutoffGaussianBlock

namespace OAI

/-! # Gaussian kernel bounds give the actual upper heat decrement -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- A scale-displacement Gaussian majorant gives the exact shell factor. -/
theorem shell_bound_of_displacement (p : X) {r C D : ℝ} (hr : 0 < r) (f : X → ℝ)
    (hbound : ∀ q : ℝ, 0 ≤ q → ∀ z, q * r ≤ dist p z →
      f z ≤ C * Real.exp (-q ^ 2 / D)) (j : ℕ) {z : X} (hz : z ∈ dyadicShell p r j) :
    f z ≤ C * gaussianShellFactor D⁻¹ j := by
  cases j with
  | zero => simpa only [gaussianShellFactor, zero_pow (by decide : 2 ≠ 0), neg_zero,
      zero_div, Real.exp_zero] using hbound 0 le_rfl z (by simpa only [zero_mul] using dist_nonneg)
  | succ j =>
    have hb := hbound (2 ^ j) (by positivity) z
      (by simpa only [dist_comm] using dyadicShell_separation p hr j hz)
    have he : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [pow_two, ← mul_pow]; norm_num
    simpa only [gaussianShellFactor, he, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using hb

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

/-- The Gaussian shell convolution controls the actual upper decrement.
The only exterior term is the explicitly decaying Gaussian times total mass. -/
theorem gaussian_dyadic_heat_increment_upper (m : ℕ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {s A D η lambda : ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hD : 0 < D)
    (hlambda0 : 0 ≤ lambda) (hlambda : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (herror : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hgaussian : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ∀ q : ℝ, 0 ≤ q → ∀ z,
      q * s ≤ dist p z → (χ.weight : X → ℝ) z * ker t p z ≤
        (A / s ^ (m + 2)) * Real.exp (-q ^ 2 / D))
    (N : ℕ) (v : Euclidean n) :
    let budget := A * gaussianMassConvolutionConstant m D⁻¹ *
      (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
        (((2 ^ j * s) ^ 2 / (2 ^ j * s) ^ (m + 2)) * (M.measure v).real (ball p (2 ^ j * s)))) +
      s ^ 2 * ((A / s ^ (m + 2)) * Real.exp (-(4 : ℝ) ^ N / D)) * (M.measure v).real univ
    ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
      U (sq_pos_of_pos hs) p lambda v⟫_ℝ -
    ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
      U (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) p lambda v⟫_ℝ ≤
      (3 / 2 : ℝ) * budget + (3 / 4 : ℝ) * s ^ 2 * (lambda + η) * ‖v‖ ^ 2 := by
  apply dyadic_heat_increment_upper_bound μ hQ hk G χ hρ hρr hκ hs hlambda0 hlambda herror v
  intro t ht htpos
  apply scaled_cutoffHeatMass_le_geometric μ hQ hk χ.weight.continuous
    (χ.hasCompactSupport μ hQ) M m p hs htpos hA (inv_pos.mpr hD)
    (by positivity) N
  · intro j _ z hz
    exact shell_bound_of_displacement p hs (fun z => (χ.weight : X → ℝ) z * ker t p z)
      (hgaussian t ht) j hz
  · intro z hz
    have hd : 2 ^ N * s ≤ dist p z := by
      simpa only [mem_ball, not_lt, dist_comm] using hz
    have hb := hgaussian t ht (2 ^ N) (by positivity) z hd
    have he : ((2 : ℝ) ^ N) ^ 2 = 4 ^ N := by rw [pow_two, ← mul_pow]; norm_num
    simpa only [he] using hb

end RegularPointCoordinates

end

end OAI
