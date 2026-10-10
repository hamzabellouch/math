import OAI.Geometry.RCD.Harmonic.HarmonicSourceIntegral
import OAI.Geometry.RCD.Harmonic.HarmonicGramSourceComparison

namespace OAI

/-! # The actual mean/heat discrepancy in the three source budgets -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

private theorem three_source_triangle (a b m₀ m₁ c₀ c₁ e₀ e₁ κ : ℝ) :
    |a - b - (2 * m₀ - 2 * κ * c₀ + e₀) - (2 * m₁ - 2 * κ * c₁ + e₁)| ≤
      |a| + |b| + 2 * (|m₀| + |m₁|) + 2 * |κ| * (|c₀| + |c₁|) + |e₀| + |e₁| := by
  have h := abs_sub (a - b - (2 * m₀ - 2 * κ * c₀ + e₀)) (2 * m₁ - 2 * κ * c₁ + e₁)
  have h' := abs_sub (a - b) (2 * m₀ - 2 * κ * c₀ + e₀)
  have hab := abs_sub a b
  have h₀ := abs_add_le (2 * m₀ - 2 * κ * c₀) e₀
  have h₁ := abs_add_le (2 * m₁ - 2 * κ * c₁) e₁
  have h₀' := abs_sub (2 * m₀) (2 * κ * c₀)
  have h₁' := abs_sub (2 * m₁) (2 * κ * c₁)
  simp only [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at h₀' h₁'
  nlinarith only [h, h', hab, h₀, h₁, h₀', h₁']

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
  (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

/-- The actual metric discrepancy is bounded by the terminal heat value,
regularizer, full positive-source integrals, curvature integrals and annular
error integrals. No comparison estimate is assumed. -/
theorem LocalHarmonicEnergy.mean_sub_heat_norm_le (hρ : 0 < ρ) (hρr : ρ < r)
    (A : Set X) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A)
    (hχA : ∀ z ∈ A, χ.weight z = 1) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (x : X) (lambda : ℝ) :
    let f := SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ.weight χ.sobolev)
    let c := fun z => χ.weight z * localGamma μ hQ (U v) (U v) z
    let e := cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian
    |⟪v, (sobolevMeanGram μ hQ U A hA -
      cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) U hs x lambda) v⟫_ℝ| ≤
      |(μ.real A)⁻¹ * (∫ z in A, heatAt μ hQ t f z ∂μ) - kernelHeat μ hQ hk t f x| +
      |lambda * s| * ‖v‖ ^ 2 +
      2 * (|∫ τ in (0 : ℝ)..s, ⟪v, cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M A hA hbounded τ v⟫_ℝ| +
        |∫ τ in s..t, ⟪v, (cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
          (χ.hasCompactSupport μ hQ) M A hA hbounded τ -
          cutoffHeatMassAt μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) M τ x) v⟫_ℝ|) +
      2 * |κ| * (|∫ τ in (0 : ℝ)..s, ∫ z, kernelAverage μ ker τ A z * c z ∂μ| +
        |∫ τ in s..t, ∫ z, (kernelAverage μ ker τ A z - ker τ x z) * c z ∂μ|) +
      |∫ τ in (0 : ℝ)..s, ∫ z, kernelAverage μ ker τ A z * e z ∂μ| +
      |∫ τ in s..t, ∫ z, (kernelAverage μ ker τ A z - ker τ x z) * e z ∂μ| := by
  dsimp only
  have hχΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r) := by
    intro z hz
    have hd := χ.tsupport_subset μ hQ hz
    rw [mem_closedBall] at hd
    exact lt_of_le_of_lt hd (by linarith)
  have hqzero : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) → χ.laplacian z = 0 := by
    filter_upwards [χ.laplacian_locality] with z hz hn
    exact hz (Or.inr (by simpa only [mem_closedBall, dist_comm, not_le] using hn))
  have hid := G.mean_sub_heat_source μ hQ hk χ.weight (χ.hasCompactSupport μ hQ)
    hχΩ χ.sobolev χ.representative χ.laplacian χ.weak_laplacian p
    (mul_pos (by norm_num) hρ)
    (fun z hz => χ.zero z (by simpa only [mem_closedBall, dist_comm, not_le] using hz)) hqzero
    A hA hbounded.measure_lt_top.ne hχA hs hst x lambda
  rw [G.integrated_average_source_components μ hQ hk χ A hA hbounded hs.le,
    G.integrated_difference_source_components μ hQ hk χ hρ A hA hbounded x hs hst] at hid
  rw [hid]
  have h := three_source_triangle
    ((μ.real A)⁻¹ * (∫ z in A, heatAt μ hQ t
      (SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ.weight χ.sobolev)) z ∂μ) -
      kernelHeat μ hQ hk t (SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ.weight χ.sobolev)) x)
    (lambda * s * ‖v‖ ^ 2)
    (∫ τ in (0 : ℝ)..s, ⟪v, cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M A hA hbounded τ v⟫_ℝ)
    (∫ τ in s..t, ⟪v, (cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M A hA hbounded τ -
      cutoffHeatMassAt μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) M τ x) v⟫_ℝ)
    (∫ τ in (0 : ℝ)..s, ∫ z, kernelAverage μ ker τ A z *
      (χ.weight z * localGamma μ hQ (U v) (U v) z) ∂μ)
    (∫ τ in s..t, ∫ z, (kernelAverage μ ker τ A z - ker τ x z) *
      (χ.weight z * localGamma μ hQ (U v) (U v) z) ∂μ)
    (∫ τ in (0 : ℝ)..s, ∫ z, kernelAverage μ ker τ A z *
      cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian z ∂μ)
    (∫ τ in s..t, ∫ z, (kernelAverage μ ker τ A z - ker τ x z) *
      cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian z ∂μ) κ
  simpa only [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)] using h

end RegularPointCoordinates

end

end OAI
