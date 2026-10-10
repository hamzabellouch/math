import OAI.Geometry.RCD.Harmonic.MetricQuadraticError
import OAI.Geometry.RCD.Coordinates.NormalizedPairing

namespace OAI

/-! # The radial value limit from Poisson height and metric approximation -/

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- The dimensionless radial value error is the sum of the Poisson height
error and the explicitly squared metric approximation error. -/
theorem radial_quadratic_value_error {n : ℕ} {p : X} {r S ε D : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hε : 0 ≤ ε) {V : X → Euclidean n}
    (hmetric : IsPointedApproximation p 0 r S ε V) (hcenter : V p = 0)
    {F : X → ℝ} {x : X} (hx : dist x p ≤ S * r)
    (hheight : |r ^ 2 * F x - dist p x ^ 2 / 2| ≤ r ^ 2 * D) :
    |F x - ‖V x‖ ^ 2 / 2| ≤ D + ε * (2 * S + ε) / 2 := by
  have hmetricx := hmetric.quadratic_value_error hr hS hε hcenter hx
  have hsum : |r ^ 2 * F x - r ^ 2 * ‖V x‖ ^ 2 / 2| ≤
      r ^ 2 * D + r ^ 2 * (ε * (2 * S + ε) / 2) :=
    (abs_sub_le (r ^ 2 * F x) (dist p x ^ 2 / 2)
      (r ^ 2 * ‖V x‖ ^ 2 / 2)).trans (add_le_add hheight hmetricx)
  have heq : r ^ 2 * F x - r ^ 2 * ‖V x‖ ^ 2 / 2 =
      r ^ 2 * (F x - ‖V x‖ ^ 2 / 2) := by ring
  rw [heq, abs_mul, abs_of_pos (sq_pos_of_pos hr)] at hsum
  nlinarith [sq_pos_of_pos hr]

/-- A bounded radial value error controls its normalized mean square.
The reference measure need only be finite on the ball. -/
theorem radial_quadratic_mean_bound (μ : Measure X) [BorelSpace X]
    {n : ℕ} {p : X} {r S ε D : ℝ} (hr : 0 < r) (hS : 0 ≤ S)
    (hε : 0 ≤ ε) (hD : 0 ≤ D) (hfin : μ (ball p (S * r)) ≠ ∞)
    {V : X → Euclidean n} (hV : Measurable V)
    (hmetric : IsPointedApproximation p 0 r S ε V) (hcenter : V p = 0)
    {F : X → ℝ} (hF : AEStronglyMeasurable F (μ.restrict (ball p (S * r))))
    (hheight : ∀ᵐ x ∂μ.restrict (ball p (S * r)),
      |r ^ 2 * F x - dist p x ^ 2 / 2| ≤ r ^ 2 * D) :
    (μ.real (ball p (S * r)))⁻¹ *
      (∫ x in ball p (S * r), (F x - ‖V x‖ ^ 2 / 2) ^ 2 ∂μ) ≤
        (D + ε * (2 * S + ε) / 2) ^ 2 := by
  let Ω := ball p (S * r)
  let C := D + ε * (2 * S + ε) / 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let e : X → ℝ := fun x => F x - ‖V x‖ ^ 2 / 2
  have hb : ∀ᵐ x ∂μ.restrict Ω, |e x| ≤ C := by
    filter_upwards [hheight, ae_restrict_mem measurableSet_ball] with x hh hx
    exact radial_quadratic_value_error hr hS hε hmetric hcenter hx.le hh
  have hmV : Measurable (fun x => ‖V x‖ ^ 2 / 2) := by fun_prop
  have hm : AEStronglyMeasurable e (μ.restrict Ω) :=
    hF.sub hmV.aestronglyMeasurable
  let : IsFiniteMeasure (μ.restrict Ω) :=
    ⟨by simpa only [Ω, Measure.restrict_apply_univ] using hfin.lt_top⟩
  have he : MemLp e 2 (μ.restrict Ω) :=
    MemLp.of_bound hm C (by simpa only [Real.norm_eq_abs] using hb)
  have hi : (∫ x in Ω, e x ^ 2 ∂μ) ≤ C ^ 2 * μ.real Ω := by
    have hb' : ∀ᵐ x ∂μ.restrict Ω, e x ^ 2 ≤ C ^ 2 := by
      filter_upwards [hb] with x hx
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr hx
    have hh := integral_mono_ae he.integrable_sq (integrable_const (C ^ 2)) hb'
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using hh
  change (μ.real Ω)⁻¹ * (∫ x in Ω, e x ^ 2 ∂μ) ≤ C ^ 2
  by_cases hz : μ.real Ω = 0
  · simp only [hz, inv_zero, zero_mul]
    positivity
  · calc
      _ ≤ (μ.real Ω)⁻¹ * (C ^ 2 * μ.real Ω) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = C ^ 2 := by field_simp

/-- Vanishing height error and vanishing metric error imply the exact
quadratic value limit needed by local Poisson/harmonic compactness. -/
theorem radial_quadratic_mean_tendsto_zero (μ : Measure X) [BorelSpace X]
    {n : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (p : ℕ → X) (r ε D : ℕ → ℝ) (V : ℕ → X → Euclidean n) (F : ℕ → X → ℝ)
    (hr : ∀ i, 0 < r i) (hε : ∀ i, 0 ≤ ε i) (hD : ∀ i, 0 ≤ D i)
    (hfin : ∀ i, μ (ball (p i) (S * r i)) ≠ ∞)
    (hV : ∀ i, Measurable (V i))
    (hmetric : ∀ i, IsPointedApproximation (p i) 0 (r i) S (ε i) (V i))
    (hcenter : ∀ i, V i (p i) = 0)
    (hF : ∀ i, AEStronglyMeasurable (F i) (μ.restrict (ball (p i) (S * r i))))
    (hheight : ∀ i, ∀ᵐ x ∂μ.restrict (ball (p i) (S * r i)),
      |r i ^ 2 * F i x - dist (p i) x ^ 2 / 2| ≤ r i ^ 2 * D i)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hD0 : Tendsto D atTop (𝓝 0)) :
    Tendsto (fun i => (μ.real (ball (p i) (S * r i)))⁻¹ *
      (∫ x in ball (p i) (S * r i), (F i x - ‖V i x‖ ^ 2 / 2) ^ 2 ∂μ))
      atTop (𝓝 0) := by
  have hbound := fun i => radial_quadratic_mean_bound μ (hr i) hS (hε i) (hD i)
    (hfin i) (hV i) (hmetric i) (hcenter i) (hF i) (hheight i)
  have hlim : Tendsto (fun i => (D i + ε i * (2 * S + ε i) / 2) ^ 2) atTop (𝓝 0) := by
    have h := (hD0.add ((hε0.mul ((tendsto_const_nhds (x := 2 * S)).add hε0)).div_const 2)).pow 2
    simpa using h
  exact squeeze_zero (fun i => mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
    hbound hlim

end RegularPointCoordinates

end

end OAI
