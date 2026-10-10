import OAI.Geometry.RCD.Coordinates.MeasuredCoordinateInput
import OAI.Geometry.RCD.Harmonic.MetricQuadraticError
import OAI.Geometry.RCD.Coordinates.MetricDyadicNormalization

namespace OAI

/-! # The actual metric coordinates on the projection ball -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- The controlled-normalization theorem uses a half-ball in units s/8.
This is the same physical ball as the radial fit's radius-four ball in
units s/64, with the exact corresponding error conversion. -/
theorem radial_metric_from_controlled {n : ℕ} {p : X} {s epsilon : ℝ}
    (hs : 0 < s) (V : X → Euclidean n)
    (hf : IsPointedApproximation p 0 (s / 8) (1 / 2) epsilon
      (fun x => (s / 8)⁻¹ • V x)) :
    IsPointedApproximation p 0 (s / 64) 4 (8 * epsilon)
      (fun x => (s / 64)⁻¹ • V x) := by
  have hrad : s / 8 = 8 * (s / 64) := by ring
  rw [hrad] at hf
  have hh := hf.rescale_eight (by positivity : 0 < s / 64)
  have hscale : (8 : ℝ) * (8 * (s / 64))⁻¹ = (s / 64)⁻¹ := by field_simp
  simpa only [smul_smul, hscale] using hh

/-- Restrict the centered metric map used by the radial fits and express
it in the length units of the two-center projection. -/
theorem projection_metric_rescale {n : ℕ} {p : X} {s delta : ℝ}
    (hs : 0 < s) (hdelta : 0 ≤ delta) (f : X → Euclidean n) (hcenter : f p = 0)
    (hf : IsPointedApproximation p 0 (s / 64) 4 delta f) :
    IsPointedApproximation p 0 s (2 * (1 / 1024)) (delta / 32)
      (fun x => (1 / 64 : ℝ) • f x) := by
  have hr : 0 < s / 64 := by positivity
  refine ⟨by simp only [hcenter, smul_zero, dist_self]; positivity, ?_, ?_⟩
  · intro x y hx hy
    have hx' : dist x p ≤ 4 * (s / 64) := by linarith
    have hy' : dist y p ≤ 4 * (s / 64) := by linarith
    have hh := hf.2.1 x y hx' hy'
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)]
    have heq : (1 / 64 : ℝ) * dist (f x) (f y) - dist x y / s =
        (1 / 64 : ℝ) * (dist (f x) (f y) - dist x y / (s / 64)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)]
    nlinarith
  · intro y hy
    have hy' : dist ((64 : ℝ) • y) (0 : Euclidean n) ≤ 4 - delta := by
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 64)]
      rw [dist_zero_right] at hy
      nlinarith
    obtain ⟨x, hx, hxy⟩ := hf.2.2 ((64 : ℝ) • y) hy'
    have hnorm : ‖f x‖ ≤ 64 * ‖y‖ + delta := by
      have hh := norm_le_norm_add_norm_sub ((64 : ℝ) • y) (f x)
      rw [norm_sub_rev ((64 : ℝ) • y) (f x)] at hh
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 64)] at hh
      rw [dist_eq_norm] at hxy
      linarith
    have hdist := (hf.centered_norm_error hr (by norm_num) hcenter hx).1
    have hdist' : dist x p / (s / 64) ≤ 64 * ‖y‖ + 2 * delta := by
      linarith [(abs_le.mp hdist).1]
    have hxsmall : dist x p ≤ (2 * (1 / 1024 : ℝ)) * s := by
      rw [dist_zero_right] at hy
      have hh : dist x p / (s / 64) ≤ 1 / 8 := by nlinarith
      have hh' := (div_le_iff₀ hr).mp hh
      linarith
    refine ⟨x, hxsmall, ?_⟩
    have hyid : y = (1 / 64 : ℝ) • ((64 : ℝ) • y) := by simp [smul_smul]
    calc
      dist ((1 / 64 : ℝ) • f x) y =
          dist ((1 / 64 : ℝ) • f x) ((1 / 64 : ℝ) • ((64 : ℝ) • y)) := by rw [← hyid]
      _ = (1 / 64 : ℝ) * dist (f x) ((64 : ℝ) • y) := by
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)]
      _ ≤ delta / 32 := by nlinarith

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
/-- The published measured-convergence input applies to the same centered
coordinates used by the radial argument, at the fixed projection radius. -/
theorem projection_measured_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hmeasured : LocalMeasuredCoordinateInput hX) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (p : X) (s : ℝ), 0 < s →
      -delta / 32 ≤ K * s ^ 2 →
      ∀ f : X → Euclidean n, Measurable f → f p = 0 →
        IsPointedApproximation p 0 (s / 64) 4 delta f →
        IsMeasuredEuclideanApproximation (hausdorff n X) n p s (1 / 1024) epsilon
          (fun x => (1 / 64 : ℝ) • f x) := by
  obtain ⟨eta, heta, happly⟩ := hmeasured hn (1 / 1024) epsilon (by norm_num) hepsilon
  refine ⟨32 * eta, by positivity, ?_⟩
  intro p s hs hcurv f hmeas hcenter hf
  apply happly p s hs (by nlinarith) (fun x => (1 / 64 : ℝ) • f x)
    ((continuous_const_smul (1 / 64 : ℝ)).measurable.comp hmeas)
  simpa only [mul_div_cancel_left₀ eta (by norm_num : (32 : ℝ) ≠ 0)] using
    projection_metric_rescale hs (by positivity : 0 ≤ 32 * eta) f hcenter hf

end RegularPointCoordinates

end

end OAI
