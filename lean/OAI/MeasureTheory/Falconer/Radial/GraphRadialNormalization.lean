import OAI.MeasureTheory.Falconer.Graphs.GraphLiftInverse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_radial_normalization (f : ℝ → ℂ) {R : ℝ} (hR : 0 < R) :
    R⁻¹ • (∫ r : ℝ, f r) = ∫ t : ℝ, f (R*t) := by
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hR)]

theorem graph_radial_interval_normalization (f : ℝ → ℂ) {R : ℝ}
    (hR : 0 < R) (a b : ℝ) :
    R⁻¹ • (∫ r in (R*a)..(R*b), f r) = ∫ t in a..b, f (R*t) := by
  rw [intervalIntegral.integral_comp_mul_left f hR.ne']

theorem graph_radial_angular_density (f : ℝ → ℂ) (z : ℝ) :
    (2/(1+z^2)) • (∫ t : ℝ, f t) =
      (Real.sqrt (1+z^2))⁻¹ • ∫ ρ : ℝ, f (ρ*Real.sqrt (1+z^2)/2) := by
  have hs : 0 < Real.sqrt (1+z^2) := Real.sqrt_pos.2 (by positivity)
  have he : (fun ρ => f (ρ*Real.sqrt (1+z^2)/2)) =
      fun ρ => f (ρ*(Real.sqrt (1+z^2)/2)) := by
    funext ρ
    congr 1
    ring
  rw [he, Measure.integral_comp_mul_right, abs_of_pos (inv_pos.mpr (half_pos hs)), smul_smul]
  congr 1
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+z^2)
  field_simp
  nlinarith

theorem graph_radial_angular_density_Ioi (f : ℝ → ℂ) (z : ℝ) :
    (2/(1+z^2)) • (∫ t in Ioi (0:ℝ), f t) =
      (Real.sqrt (1+z^2))⁻¹ • ∫ ρ in Ioi (0:ℝ), f (ρ*Real.sqrt (1+z^2)/2) := by
  have hs : 0 < Real.sqrt (1+z^2) := Real.sqrt_pos.2 (by positivity)
  have he : (fun ρ => f (ρ*Real.sqrt (1+z^2)/2)) =
      fun ρ => f (ρ*(Real.sqrt (1+z^2)/2)) := by
    funext ρ
    congr 1
    ring
  rw [he, integral_comp_mul_right_Ioi f 0 (half_pos hs), zero_mul, smul_smul]
  congr 1
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+z^2)
  field_simp
  nlinarith

theorem graph_radial_angular_density_interval (f : ℝ → ℂ) (z a b : ℝ) :
    (2/(1+z^2)) • (∫ t in a..b, f t) =
      (Real.sqrt (1+z^2))⁻¹ •
        ∫ ρ in (2*a/Real.sqrt (1+z^2))..(2*b/Real.sqrt (1+z^2)),
          f (ρ*Real.sqrt (1+z^2)/2) := by
  have hs : 0 < Real.sqrt (1+z^2) := Real.sqrt_pos.2 (by positivity)
  have he : (fun ρ => f (ρ*Real.sqrt (1+z^2)/2)) =
      fun ρ => f (ρ*(Real.sqrt (1+z^2)/2)) := by
    funext ρ
    congr 1
    ring
  have ha : (2*a/Real.sqrt (1+z^2))*(Real.sqrt (1+z^2)/2) = a := by field_simp
  have hb : (2*b/Real.sqrt (1+z^2))*(Real.sqrt (1+z^2)/2) = b := by field_simp
  rw [he, intervalIntegral.integral_comp_mul_right f (half_pos hs).ne', ha, hb, smul_smul]
  congr 1
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+z^2)
  field_simp
  nlinarith

end PlanarFalconer

end OAI
