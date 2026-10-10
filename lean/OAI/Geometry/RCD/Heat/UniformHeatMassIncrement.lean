import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.HeatMassIncrement

namespace OAI

/-! # Uniform dyadic heat lower bounds with the correct mass scaling -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Gaussian lower constants are fixed before choosing the scale or pole.
Only the stated local volume upper bounds are needed on the testing set. -/
theorem uniform_gaussian_lower_time_block (μ : Measure X) {ker : ℝ → X → X → ℝ}
    (hg : HasCoordinateHeatBounds μ ker) (n : ℕ)
    {V A : ℝ} (hV : 0 < V) (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ r, 0 < r → r ≤ 1 → ∀ (x : X) (S : Set X),
      (∀ t, r ^ 2 / 4 ≤ t → t ≤ r ^ 2 → ∀ y ∈ S,
        0 < μ.real (ball y (Real.sqrt t)) ∧ μ.real (ball y (Real.sqrt t)) ≤ V * r ^ n) →
      (∀ y ∈ S, (dist x y) ^ 2 ≤ A * r ^ 2) →
      ∀ t, r ^ 2 / 4 ≤ t → t ≤ r ^ 2 → ∀ y ∈ S, c / r ^ n ≤ ker t x y := by
  obtain ⟨L,hL,hlower⟩ := hg.localLower (4*A) (by positivity)
  refine ⟨L/V,div_pos hL hV,?_⟩
  intro r hr hr1 x S hvolume hdist t hlow hupp y hy
  have ht : 0 < t := (div_pos (sq_pos_of_pos hr) (by norm_num)).trans_le hlow
  have ht1 : t ≤ 1 := hupp.trans (by nlinarith)
  have hd : (dist x y)^2 ≤ (4*A)*t := by
    have hm := mul_le_mul_of_nonneg_left hlow hA
    nlinarith [hdist y hy]
  have hv := hvolume t hlow hupp y hy
  calc
    (L/V)/r^n = L/(V*r^n) := by ring
    _ ≤ L/μ.real (ball y (Real.sqrt t)) := div_le_div_of_nonneg_left hL.le hv.1 hv.2
    _ ≤ ker t x y := hlower t ht ht1 x y hd

variable [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

/-- On a dyadic time block the actual heat decrement dominates the local
mass with its dimensionless factor r²/rⁿ. The mass is the full measure. -/
theorem dyadic_heat_increment_lower_mass (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    (S : Set X) (hS : MeasurableSet S) (hχone : ∀ y ∈ S, (χ.weight : X → ℝ) y = 1)
    {s c η lambda : ℝ} (hs : 0 < s) (hlambda0 : 0 ≤ lambda)
    (hlambda : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (herror : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hkernel : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ∀ y ∈ S, c / s ^ n ≤ ker t p y)
    (v : Euclidean n) :
    ((3 * c / 2) * (s ^ 2 / s ^ n)) * ⟪v, M.massOperator S v⟫_ℝ ≤
      ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U (sq_pos_of_pos hs) p lambda v⟫_ℝ -
      ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) p lambda v⟫_ℝ := by
  have hb := harmonic_heat_increment_lower_mass μ hQ hk G χ hρ hρr hκ S hS hχone
    (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4))
    (show s ^ 2 / 4 ≤ s ^ 2 by nlinarith [sq_nonneg s]) hlambda0 hlambda herror hkernel v
  convert hb using 1
  ring

end RegularPointCoordinates

end

end OAI
