import OAI.Geometry.IsometricImmersion.Calculus.MovingIntervalCalculus
import OAI.Geometry.IsometricImmersion.Caps.EnergyCauchySchwarz

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def movingEnergy (xl xr theta0 speed : ℝ) (S v : Coord → ℝ) : ℝ → ℝ :=
  movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
    (energyDensity S v)

def movingEnergyRate (xl xr theta0 speed : ℝ) (P S bTheta bXi v R : Coord → ℝ)
    (theta : ℝ) : ℝ :=
  energyFlux P S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) -
    energyFlux P S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta) -
    speed * (energyDensity S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) +
      energyDensity S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta)) +
    movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) theta

def movingSourceNorm (xl xr theta0 speed : ℝ) (R : Coord → ℝ) (theta : ℝ) : ℝ :=
  Real.sqrt (movingIntervalIntegral (inwardLeft xl theta0 speed)
    (inwardRight xr theta0 speed) (fun p => R p ^ 2) theta)

theorem interval_product_abs_le_sqrt_squares
    {f g : ℝ → ℝ} {xl xr : ℝ} (hlr : xl ≤ xr)
    (hf : ContinuousOn f (Icc xl xr)) (hg : ContinuousOn g (Icc xl xr)) :
    |∫ x in xl..xr, f x * g x| ≤
      Real.sqrt (∫ x in xl..xr, f x ^ 2) * Real.sqrt (∫ x in xl..xr, g x ^ 2) := by
  have hf2 : MemLp f 2 (volume.restrict (Icc xl xr)) :=
    (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).2
      ((hf.pow 2).integrableOn_compact isCompact_Icc)
  have hg2 : MemLp g 2 (volume.restrict (Icc xl xr)) :=
    (memLp_two_iff_integrable_sq (hg.aestronglyMeasurable measurableSet_Icc)).2
      ((hg.pow 2).integrableOn_compact isCompact_Icc)
  simpa only [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc] using
    integral_product_abs_le_sqrt_squares hf2 hg2

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem movingEnergy_hasDerivAt
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hradius : 0 < radius)
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hEq : ∀ p ∈ coordinateRectangle radius lo hi, hyperbolicOperator P S v p =
      bTheta p * coordPartial 1 v p + bXi p * coordPartial 0 v p + R p) :
    HasDerivAt (movingEnergy xl xr theta0 speed S v)
      (movingEnergyRate xl xr theta0 speed P S bTheta bXi v R theta) theta := by
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  obtain ⟨he, hj, herr⟩ := energy_fields_contDiffOn hU hP hS hbt hbx hv
  have hrest : ContDiffOn ℝ ∞
      (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) U :=
    herr.add (hR.mul (partial_contDiffOn hv hU 1))
  have hmem {x : ℝ}
      (hx : x ∈ uIcc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordinatePoint x theta ∈ U :=
    point_mem_rectangle
      ⟨lt_of_lt_of_le (lt_min hl.1 hr.1) hx.1,
        lt_of_le_of_lt hx.2 (max_lt hl.2 hr.2)⟩ htheta
  have hlocal (p : Coord) (hp : p ∈ U) :
      coordPartial 1 (energyDensity S v) p =
        coordPartial 0 (energyFlux P S v) p +
          (energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) := by
    have hh := energy_density_flux_identity
      ((hP.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
      ((hS.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) hv hU hp (hEq p hp)
    linarith
  have hint :
      (∫ x in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
        coordPartial 1 (energyDensity S v) (coordinatePoint x theta)) =
      energyFlux P S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) -
        energyFlux P S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta) +
      movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
        (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) theta := by
    calc
      _ = ∫ x in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
          coordPartial 0 (energyFlux P S v) (coordinatePoint x theta) +
            (energyCoefficientError P S bTheta bXi v (coordinatePoint x theta) +
              R (coordinatePoint x theta) * coordPartial 1 v (coordinatePoint x theta)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hlocal _ (hmem hx)
      _ = _ := by
        rw [intervalIntegral.integral_add
          (slice_intervalIntegrable (partial_contDiffOn hj hU 0).continuousOn hl hr htheta)
          (slice_intervalIntegrable hrest.continuousOn hl hr htheta),
          slice_integral_partial_xi hj hl hr htheta]
        rfl
  have hd := inwardIntervalIntegral_hasDerivAt he hradius hl hr htheta
  rw [hint] at hd
  convert hd using 1
  · rfl
  · dsimp only [movingEnergyRate]
    ring

theorem movingEnergy_nonneg
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    (hS : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      0 ≤ S (coordinatePoint x theta)) :
    0 ≤ movingEnergy xl xr theta0 speed S v theta := by
  exact intervalIntegral.integral_nonneg hlr (fun x hx => energyDensity_nonneg (hS x hx))

theorem moving_source_integral_bound
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    (hSpos : ∀ p ∈ coordinateRectangle radius lo hi, 0 ≤ S p) :
    movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (fun p => R p * coordPartial 1 v p) theta ≤
      Real.sqrt (2 * movingEnergy xl xr theta0 speed S v theta) *
        movingSourceNorm xl xr theta0 speed R theta := by
  let l := inwardLeft xl theta0 speed theta
  let r := inwardRight xr theta0 speed theta
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  have hmem {x : ℝ} (hx : x ∈ Icc l r) : coordinatePoint x theta ∈ U :=
    point_mem_rectangle ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩ htheta
  have hvt := partial_contDiffOn hv hU 1
  have hx := partial_contDiffOn hv hU 0
  have he : ContDiffOn ℝ ∞ (energyDensity S v) U :=
    ((hvt.pow 2).add (hS.mul (hx.pow 2))).div_const 2
  have he2 : ContDiffOn ℝ ∞ (fun p => 2 * energyDensity S v p) U :=
    contDiffOn_const.mul he
  have hcR : ContinuousOn (fun x => R (coordinatePoint x theta)) (Icc l r) :=
    hR.continuousOn.comp (by unfold coordinatePoint; fun_prop) (fun x hx => hmem hx)
  have hcvt : ContinuousOn (fun x => coordPartial 1 v (coordinatePoint x theta)) (Icc l r) :=
    hvt.continuousOn.comp (by unfold coordinatePoint; fun_prop) (fun x hx => hmem hx)
  have hC := interval_product_abs_le_sqrt_squares hlr hcR hcvt
  have hkin : (∫ x in l..r, (coordPartial 1 v (coordinatePoint x theta)) ^ 2) ≤
      2 * movingEnergy xl xr theta0 speed S v theta := by
    have hI := intervalIntegral.integral_mono_on hlr
      (slice_intervalIntegrable (hvt.pow 2).continuousOn hl hr htheta)
      (slice_intervalIntegrable he2.continuousOn hl hr htheta)
      (fun x hx => by
        have hs := hSpos _ (hmem hx)
        unfold energyDensity
        nlinarith [mul_nonneg hs (sq_nonneg (coordPartial 0 v (coordinatePoint x theta)))])
    simpa only [movingEnergy, movingIntervalIntegral, intervalIntegral.integral_const_mul] using hI
  have hroot := Real.sqrt_le_sqrt hkin
  have hmul := mul_le_mul_of_nonneg_left hroot
    (Real.sqrt_nonneg (∫ x in l..r, R (coordinatePoint x theta) ^ 2))
  unfold movingIntervalIntegral movingSourceNorm
  exact (le_abs_self _).trans (hC.trans
    (by simpa only [l, r, movingIntervalIntegral, mul_comm] using hmul))

theorem movingEnergyRate_le
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    {s0 M : ℝ} (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ p ∈ coordinateRectangle radius lo hi, s0 ≤ S p)
    (hcoeff : ∀ p ∈ coordinateRectangle radius lo hi,
      |bTheta p| ≤ M ∧ |bXi p| ≤ M ∧ |coordPartial 0 P p| ≤ M ∧
        |coordPartial 0 S p| ≤ M ∧ |coordPartial 1 S p| ≤ M)
    (hspeed : ∀ p ∈ coordinateRectangle radius lo hi, |P p| + Real.sqrt (S p) ≤ speed) :
    movingEnergyRate xl xr theta0 speed P S bTheta bXi v R theta ≤
      (8 * M * (1 + 1 / s0)) * movingEnergy xl xr theta0 speed S v theta +
      Real.sqrt (2 * movingEnergy xl xr theta0 speed S v theta) *
        movingSourceNorm xl xr theta0 speed R theta := by
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  obtain ⟨he, hj, herr⟩ := energy_fields_contDiffOn hU hP hS hbt hbx hv
  have heC : ContDiffOn ℝ ∞
      (fun p => (8 * M * (1 + 1 / s0)) * energyDensity S v p) U :=
    contDiffOn_const.mul he
  have hsource := hR.mul (partial_contDiffOn hv hU 1)
  have hmem {x : ℝ}
      (hx : x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordinatePoint x theta ∈ U :=
    point_mem_rectangle ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩ htheta
  have hSl := hSfloor _ (point_mem_rectangle hl htheta)
  have hSr := hSfloor _ (point_mem_rectangle hr htheta)
  have hboundary := inward_boundary_nonpositive (v := v) (hs0.le.trans hSl) (hs0.le.trans hSr)
    (hspeed _ (point_mem_rectangle hl htheta)) (hspeed _ (point_mem_rectangle hr htheta))
  have herrI : movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (energyCoefficientError P S bTheta bXi v) theta ≤
      (8 * M * (1 + 1 / s0)) * movingEnergy xl xr theta0 speed S v theta := by
    have hh := intervalIntegral.integral_mono_on hlr
      (slice_intervalIntegrable herr.continuousOn hl hr htheta)
      (slice_intervalIntegrable heC.continuousOn hl hr htheta)
      (fun x hx => by
        obtain ⟨hbt', hbx', hPx', hSx', hSt'⟩ := hcoeff _ (hmem hx)
        exact (le_abs_self _).trans (energyCoefficientError_abs_le hs0
          (hSfloor _ (hmem hx)) hM hbt' hbx' hPx' hSx' hSt'))
    simpa only [movingIntervalIntegral, movingEnergy, intervalIntegral.integral_const_mul] using hh
  have hsourceI := moving_source_integral_bound hS hv hR hl hr htheta hlr
    (fun p hp => hs0.le.trans (hSfloor p hp))
  unfold movingEnergyRate movingIntervalIntegral
  rw [intervalIntegral.integral_add
    (slice_intervalIntegrable herr.continuousOn hl hr htheta)
    (slice_intervalIntegrable hsource.continuousOn hl hr htheta)]
  dsimp only [movingIntervalIntegral] at herrI hsourceI
  linarith

end SmoothLocal.Hyperbolic

end

end OAI
