import OAI.Geometry.IsometricImmersion.Energy.WeightPrimitiveParameter
import OAI.Geometry.IsometricImmersion.Energy.HyperbolicEnergyDensity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def movingIntervalIntegral (left right : ℝ → ℝ) (f : Coord → ℝ) (theta : ℝ) : ℝ :=
  ∫ xi in left theta..right theta, f (coordinatePoint xi theta)

def inwardLeft (x0 theta0 speed : ℝ) (theta : ℝ) : ℝ :=
  x0 + speed * (theta - theta0)

def inwardRight (x0 theta0 speed : ℝ) (theta : ℝ) : ℝ :=
  x0 - speed * (theta - theta0)

theorem inwardLeft_hasDerivAt (x0 theta0 speed theta : ℝ) :
    HasDerivAt (inwardLeft x0 theta0 speed) speed theta := by
  unfold inwardLeft
  simpa only [inwardLeft, mul_one, id_eq] using
    (((hasDerivAt_id theta).sub_const theta0).const_mul speed).const_add x0

theorem inwardRight_hasDerivAt (x0 theta0 speed theta : ℝ) :
    HasDerivAt (inwardRight x0 theta0 speed) (-speed) theta := by
  unfold inwardRight
  simpa only [inwardRight, mul_one, zero_sub, id_eq, Pi.sub_def] using
    (hasDerivAt_const theta x0).sub
      (((hasDerivAt_id theta).sub_const theta0).const_mul speed)

theorem inward_interval_length (xl xr theta0 speed theta : ℝ) :
    inwardRight xr theta0 speed theta - inwardLeft xl theta0 speed theta =
      xr - xl - 2 * speed * (theta - theta0) := by
  unfold inwardRight inwardLeft
  ring

theorem movingPoint_hasDerivAt {x : ℝ → ℝ} {dx theta : ℝ}
    (hx : HasDerivAt x dx theta) :
    HasDerivAt (fun t => coordinatePoint (x t) t)
      (dx • Pi.single 0 (1 : ℝ) + Pi.single 1 (1 : ℝ) : Coord) theta := by
  simpa only [coordinatePoint, one_smul, id_eq, Pi.add_def] using
    (hx.smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
      ((hasDerivAt_id theta).smul_const (Pi.single 1 (1 : ℝ) : Coord))

theorem slice_intervalIntegrable
    {f : Coord → ℝ} {radius lo hi xl xr theta : ℝ}
    (hf : ContinuousOn f (coordinateRectangle radius lo hi))
    (hxl : xl ∈ Ioo (-radius) radius) (hxr : xr ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    IntervalIntegrable (fun xi => f (coordinatePoint xi theta)) volume xl xr := by
  have hc : ContinuousOn (fun xi => f (coordinatePoint xi theta)) (Ioo (-radius) radius) :=
    hf.comp (by unfold coordinatePoint; fun_prop) (fun xi hxi => point_mem_rectangle hxi htheta)
  exact (hc.mono (fun xi hxi =>
    ⟨lt_of_lt_of_le (lt_min hxl.1 hxr.1) hxi.1,
      lt_of_le_of_lt hxi.2 (max_lt hxl.2 hxr.2)⟩)).intervalIntegrable

theorem movingIntervalIntegral_eq_primitive
    {f : Coord → ℝ} {left right : ℝ → ℝ} {radius lo hi theta : ℝ}
    (hf : ContinuousOn f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : left theta ∈ Ioo (-radius) radius) (hr : right theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    movingIntervalIntegral left right f theta =
      coordinatePrimitive f (coordinatePoint (right theta) theta) -
      coordinatePrimitive f (coordinatePoint (left theta) theta) := by
  have h0 : (0 : ℝ) ∈ Ioo (-radius) radius := ⟨by linarith, hradius⟩
  have hrI := slice_intervalIntegrable hf h0 hr htheta
  have hlI := slice_intervalIntegrable hf h0 hl htheta
  simpa [movingIntervalIntegral, coordinatePrimitive, coordinatePoint] using
    (intervalIntegral.integral_interval_sub_left hrI hlI).symm

theorem movingPrimitive_hasDerivAt
    {f : Coord → ℝ} {x : ℝ → ℝ} {radius lo hi theta dx : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hx : HasDerivAt x dx theta) (hxt : x theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt (fun t => coordinatePrimitive f (coordinatePoint (x t) t))
      (dx * f (coordinatePoint (x theta) theta) +
        ∫ xi in 0..x theta, coordPartial 1 f (coordinatePoint xi theta)) theta := by
  have hp := point_mem_rectangle hxt htheta
  have hd : DifferentiableAt ℝ (coordinatePrimitive f) (coordinatePoint (x theta) theta) :=
    ((coordinatePrimitive_contDiffOn hf).contDiffAt
      ((coordinateRectangle_isOpen radius lo hi).mem_nhds hp)).differentiableAt (by simp)
  have hchain := HasFDerivAt.comp_hasDerivAt theta
    (f := fun t => coordinatePoint (x t) t) hd.hasFDerivAt
    (movingPoint_hasDerivAt (x := x) hx)
  have ht := coordinatePrimitive_partial_t hf hradius hp
  have hs := coordinatePrimitive_partial_s hf hradius hp
  simp only [coordPartial] at ht hs
  simp only [map_add, map_smul,
    smul_eq_mul, ht, hs] at hchain
  simpa [coordinatePoint, coordPartial, Function.comp_def] using hchain

theorem movingIntervalIntegral_hasDerivAt
    {f : Coord → ℝ} {left right : ℝ → ℝ} {radius lo hi theta dl dr : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : HasDerivAt left dl theta) (hr : HasDerivAt right dr theta)
    (hlt : left theta ∈ Ioo (-radius) radius)
    (hrt : right theta ∈ Ioo (-radius) radius) (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt (movingIntervalIntegral left right f)
      ((∫ xi in left theta..right theta, coordPartial 1 f (coordinatePoint xi theta)) +
        dr * f (coordinatePoint (right theta) theta) -
        dl * f (coordinatePoint (left theta) theta)) theta := by
  have hright := movingPrimitive_hasDerivAt hf hradius hr hrt htheta
  have hleft := movingPrimitive_hasDerivAt hf hradius hl hlt htheta
  have hdiff := hright.sub hleft
  have h0 : (0 : ℝ) ∈ Ioo (-radius) radius := ⟨by linarith, hradius⟩
  have hf1 := (partial_contDiffOn hf (coordinateRectangle_isOpen radius lo hi) 1).continuousOn
  have hIsub := intervalIntegral.integral_interval_sub_left
    (slice_intervalIntegrable hf1 h0 hrt htheta)
    (slice_intervalIntegrable hf1 h0 hlt htheta)
  have he :
      (dr * f (coordinatePoint (right theta) theta) +
        ∫ xi in 0..right theta, coordPartial 1 f (coordinatePoint xi theta)) -
      (dl * f (coordinatePoint (left theta) theta) +
        ∫ xi in 0..left theta, coordPartial 1 f (coordinatePoint xi theta)) =
      (∫ xi in left theta..right theta, coordPartial 1 f (coordinatePoint xi theta)) +
        dr * f (coordinatePoint (right theta) theta) -
        dl * f (coordinatePoint (left theta) theta) := by linarith
  rw [he] at hdiff
  apply hdiff.congr_of_eventuallyEq
  filter_upwards [hl.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hlt),
    hr.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hrt),
    isOpen_Ioo.mem_nhds htheta] with t hlt' hrt' ht'
  exact movingIntervalIntegral_eq_primitive hf.continuousOn hradius hlt' hrt' ht'

theorem inwardIntervalIntegral_hasDerivAt
    {f : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt
      (movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed) f)
      ((∫ xi in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
          coordPartial 1 f (coordinatePoint xi theta)) -
        speed * (f (coordinatePoint (inwardRight xr theta0 speed theta) theta) +
          f (coordinatePoint (inwardLeft xl theta0 speed theta) theta))) theta := by
  convert movingIntervalIntegral_hasDerivAt hf hradius
    (inwardLeft_hasDerivAt xl theta0 speed theta)
    (inwardRight_hasDerivAt xr theta0 speed theta) hl hr htheta using 1
  ring

theorem slice_integral_partial_xi
    {f : Coord → ℝ} {radius lo hi xl xr theta : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi))
    (hxl : xl ∈ Ioo (-radius) radius) (hxr : xr ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    (∫ xi in xl..xr, coordPartial 0 f (coordinatePoint xi theta)) =
      f (coordinatePoint xr theta) - f (coordinatePoint xl theta) := by
  have hmem {xi : ℝ} (hxi : xi ∈ uIcc xl xr) :
      coordinatePoint xi theta ∈ coordinateRectangle radius lo hi :=
    point_mem_rectangle
      ⟨lt_of_lt_of_le (lt_min hxl.1 hxr.1) hxi.1,
        lt_of_le_of_lt hxi.2 (max_lt hxl.2 hxr.2)⟩ htheta
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro xi hxi
    have hd : DifferentiableAt ℝ f (coordinatePoint xi theta) :=
      (hf.contDiffAt ((coordinateRectangle_isOpen radius lo hi).mem_nhds
        (hmem hxi))).differentiableAt (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt xi (point_hasDerivAt_t xi theta)
  · exact slice_intervalIntegrable
      (partial_contDiffOn hf (coordinateRectangle_isOpen radius lo hi) 0).continuousOn
      hxl hxr htheta

end SmoothLocal.Hyperbolic

end

end OAI
