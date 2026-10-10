import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.LongBoundedSource
import OAI.Geometry.RCD.Sobolev.CutoffEnergyBound
import OAI.Geometry.RCD.Harmonic.AveragedLpPairing

namespace OAI

/-! # The terminal heat value in the actual Gram comparison -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

include hk in
/-- At the fixed terminal time R², the genuine bounded cutoff energy
acquires the averaging displacement ratio r/R. -/
theorem exists_harmonic_endpoint_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (n : ℕ) {A V W : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r : ℝ) (x q : X),
      0 < R → R ≤ 1 → 0 < r → r ≤ R / 2 →
      μ (ball q r) ≠ ∞ → 0 < μ.real (ball q r) → dist x q ≤ A * r →
      μ.real (ball x R) ≤ W * R ^ n →
      (∀ z ∈ ball x R, V * R ^ n ≤ μ.real (ball z R)) →
      ∀ (U : E →L[ℝ] SobolevSpace μ hQ) (M : PositiveBilinearMeasure X E)
        (κ : ℝ) (p : X) (s : ℝ) (L : ℝ≥0) (v : E)
        (G : LocalHarmonicEnergy μ hQ U M κ p s L v) (χ : X →ᵇ ℝ),
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) → tsupport (χ : X → ℝ) ⊆ ball p (2 * s) →
      (∀ z ∉ ball x R, χ z = 0) → ∀ (c : SobolevSpace μ hQ),
      SobolevSpace.toLp μ hQ c =ᵐ[μ] χ →
      |(μ.real (ball q r))⁻¹ * (∫ y in ball q r,
        heatAt μ hQ (R ^ 2) (SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c)) y ∂μ) -
        kernelHeat μ hQ hk (R ^ 2) (SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c)) x| ≤
        C * ((L : ℝ) ^ 2 * ‖v‖ ^ 2) * (r / R) := by
  obtain ⟨C, hC, hb⟩ := exists_long_bounded_source_bound μ hQ hk hg hdiff n hA hV hW
  refine ⟨C, hC, ?_⟩
  intro R r x q hR hR1 hr hrR hfinite hvol hcenter hupper hsource U M κ p s L v G χ hχ hχΩ hzero c hc
  let f := SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c)
  have ht := sq_pos_of_pos hR
  have hupper' : ∀ j ≤ 0, μ.real (ball x ((2 : ℝ) ^ j * (R / (2 : ℝ) ^ 0))) ≤
      W * ((2 : ℝ) ^ j * (R / (2 : ℝ) ^ 0)) ^ n := by
    intro j hj
    have : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [this, pow_zero, div_one, one_mul] using hupper
  have hsqrt : Real.sqrt (R ^ 2) = R := Real.sqrt_sq hR.le
  have he := hb R hR hR1 0 r x q hr (by simpa using hrR) hfinite hvol hcenter hupper'
    (R ^ 2) ht (by simp only [pow_zero, div_one, mem_Icc]; constructor <;> nlinarith [sq_nonneg R])
    (by simpa only [hsqrt] using hsource) f ((L : ℝ) ^ 2 * ‖v‖ ^ 2) (by positivity)
    (G.cutoffEnergy_bound μ hQ χ hχ c hc) (G.cutoffEnergy_zero_off μ hQ χ c hc hzero)
  have hid := kernelAverage_difference_integral_lp μ hQ hk ht
    (ball q r) measurableSet_ball hfinite x f
  have havg := kernelAverage_integral_lp_eq_average μ hQ hk ht
    (ball q r) measurableSet_ball hfinite f
  rw [hid, ← kernelAverage_integral_lp μ hQ hk ht (ball q r) measurableSet_ball hfinite f, havg] at he
  simpa only [pow_zero, div_one, f] using he

end RegularPointCoordinates

end

end OAI
