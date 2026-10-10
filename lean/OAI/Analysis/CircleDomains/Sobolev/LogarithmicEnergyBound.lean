import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! Integrating the circle energy inequality against dt/t produces the
logarithmic factor in the coordinate modulus. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem logarithmic_radial_bound {E : ℝ → ℝ} {r R B K : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hE : ContinuousOn E (Icc r R))
    (hcircle : ∀ t ∈ Ioo r R, B ≤ K*t^2*E t) :
    B*Real.log (R/r) ≤ K*(∫ t in r..R, t*E t) := by
  have hR : 0 < R := hr.trans_le hrR
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Icc r R) :=
    continuousOn_id.inv₀ (fun t ht => ne_of_gt (hr.trans_le ht.1))
  have hi : IntervalIntegrable (fun t => B*t⁻¹) volume r R :=
    (continuousOn_const.mul hinv).intervalIntegrable_of_Icc hrR
  have he : IntervalIntegrable (fun t => K*(t*E t)) volume r R :=
    (continuousOn_const.mul (continuousOn_id.mul hE)).intervalIntegrable_of_Icc hrR
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hrR hi he (fun t ht => by
    have ht0 : 0 < t := hr.trans ht.1
    have h : B ≤ (K*(t*E t))*t := by nlinarith [hcircle t ht]
    simpa only [div_eq_mul_inv] using (div_le_iff₀ ht0).mpr h)
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr hR,
    intervalIntegral.integral_const_mul] at hle
  exact hle

 theorem logarithmic_radial_energy_bound {E : ℝ → ℝ} {r R A K : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hE : ContinuousOn E (Icc r R))
    (hcircle : ∀ t ∈ Ioo r R, A^2 ≤ K*t^2*E t) :
    A^2*Real.log (R/r) ≤ K*(∫ t in r..R, t*E t) :=
  logarithmic_radial_bound hr hrR hE hcircle

end CircleDomainRigidity

end

end OAI
