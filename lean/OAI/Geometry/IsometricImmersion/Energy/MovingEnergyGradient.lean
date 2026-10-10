import OAI.Geometry.IsometricImmersion.Energy.MovingSlabEnergy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem scalar_gradient_le_energy {s0 S a b : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S) :
    a ^ 2 + b ^ 2 ≤ (2 * (1 + 1 / s0)) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hspos : 0 ≤ S := hs0.le.trans hS
  have hsb : b ^ 2 ≤ (S * b ^ 2) / s0 := (le_div_iff₀ hs0).2
    (by nlinarith [mul_le_mul_of_nonneg_right hS (sq_nonneg b)])
  have hsb' : b ^ 2 ≤ (1 / s0) * (S * b ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using hsb
  have hi : 0 ≤ 1 / s0 := by positivity
  nlinarith [mul_nonneg hi (sq_nonneg a), mul_nonneg hspos (sq_nonneg b)]

theorem moving_gradient_integral_le_energy
    {S v : Coord → ℝ} {radius lo hi xl xr theta0 speed theta s0 : ℝ}
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    (hs0 : 0 < s0)
    (hfloor : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      s0 ≤ S (coordinatePoint x theta)) :
    movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (fun p => (coordPartial 1 v p) ^ 2 + (coordPartial 0 v p) ^ 2) theta ≤
      (2 * (1 + 1 / s0)) * movingEnergy xl xr theta0 speed S v theta := by
  have hU := coordinateRectangle_isOpen radius lo hi
  have ht := partial_contDiffOn hv hU 1
  have hx := partial_contDiffOn hv hU 0
  have he : ContDiffOn ℝ ∞ (energyDensity S v) (coordinateRectangle radius lo hi) :=
    ((ht.pow 2).add (hS.mul (hx.pow 2))).div_const 2
  have hgrad : ContDiffOn ℝ ∞
      (fun p => (coordPartial 1 v p) ^ 2 + (coordPartial 0 v p) ^ 2)
      (coordinateRectangle radius lo hi) := (ht.pow 2).add (hx.pow 2)
  have hconst : ContDiffOn ℝ ∞
      (fun p => (2 * (1 + 1 / s0)) * energyDensity S v p)
      (coordinateRectangle radius lo hi) := contDiffOn_const.mul he
  have hi := intervalIntegral.integral_mono_on hlr
    (slice_intervalIntegrable hgrad.continuousOn hl hr htheta)
    (slice_intervalIntegrable hconst.continuousOn hl hr htheta)
    (fun x hx => scalar_gradient_le_energy hs0 (hfloor x hx))
  simpa only [movingIntervalIntegral, movingEnergy, intervalIntegral.integral_const_mul] using hi

theorem sectionFour_inward_interval
    {L r theta : ℝ} (hL : 0 < L) (hr : 0 < r) (htheta : theta ∈ Icc (-r) r) :
    Icc (-(L * r) / 2) (L * r / 2) ⊆
      Icc (inwardLeft (-(L * r)) (-r) (L / 4) theta)
        (inwardRight (L * r) (-r) (L / 4) theta) ∧
    0 < L * r ∧ L * r ≤
      inwardRight (L * r) (-r) (L / 4) theta -
        inwardLeft (-(L * r)) (-r) (L / 4) theta := by
  have hLt := mul_le_mul_of_nonneg_left htheta.2 hL.le
  have hLr : 0 < L * r := mul_pos hL hr
  constructor
  · intro x hx
    unfold inwardLeft inwardRight
    constructor <;> nlinarith [hx.1, hx.2]
  constructor
  · exact hLr
  · unfold inwardLeft inwardRight
    nlinarith

theorem sectionFour_pulse_in_shrinkingSlab
    {L r x theta delta tau : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hwidth : delta / (2 * tau) ≤ r) (hx : |x| ≤ L * r / 16)
    (htheta : |theta| ≤ delta / (2 * tau)) :
    coordinatePoint x theta ∈ shrinkingSlab (-(L * r)) (L * r) (-r) r (L / 4) := by
  have ht : theta ∈ Icc (-r) r := by
    obtain ⟨htl, htr⟩ := abs_le.mp (htheta.trans hwidth)
    exact ⟨htl, htr⟩
  apply point_mem_shrinkingSlab ht
  apply (sectionFour_inward_interval hL hr ht).1
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  have hLr := mul_pos hL hr
  constructor <;> nlinarith

end SmoothLocal.Hyperbolic

end

end OAI
