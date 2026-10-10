import OAI.Geometry.IsometricImmersion.Energy.SqrtEnergyGronwall

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem inward_interval_geometry
    {xl xr a b speed radius t : ℝ} (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (hlength : 2 * speed * (b - a) < xr - xl) (ht : t ∈ Icc a b) :
    inwardLeft xl a speed t ∈ Ioo (-radius) radius ∧
    inwardRight xr a speed t ∈ Ioo (-radius) radius ∧
    inwardLeft xl a speed t < inwardRight xr a speed t ∧
    0 < xr - xl - 2 * speed * (b - a) ∧
    xr - xl - 2 * speed * (b - a) ≤
      inwardRight xr a speed t - inwardLeft xl a speed t := by
  have hinc : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
  have hmax := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hspeed
  have hspan : 0 ≤ speed * (b - a) := mul_nonneg hspeed (sub_nonneg.mpr hab)
  have hupper : speed * (t - a) < xr - xl := by
    linarith only [hmax, hspan, hlength]
  unfold inwardLeft inwardRight
  constructor
  · constructor
    · linarith
    · linarith only [hupper, hxr]
  constructor
  · constructor <;> linarith
  constructor
  · linarith
  constructor <;> linarith

theorem movingSourceNorm_continuousOn
    {R : Coord → ℝ} {radius lo hi xl xr a b speed : ℝ}
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hleft : ∀ t ∈ Icc a b, inwardLeft xl a speed t ∈ Ioo (-radius) radius)
    (hright : ∀ t ∈ Icc a b, inwardRight xr a speed t ∈ Ioo (-radius) radius)
    (htime : Icc a b ⊆ Ioo lo hi) :
    ContinuousOn (movingSourceNorm xl xr a speed R) (Icc a b) := by
  intro t ht
  have hd := inwardIntervalIntegral_hasDerivAt (hR.pow 2) hradius
    (hleft t ht) (hright t ht) (htime ht)
  exact hd.continuousAt.sqrt.continuousWithinAt

theorem moving_energy_propagation
    {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr a b speed s0 M : ℝ}
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hradius : 0 < radius) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlength : 2 * speed * (b - a) < xr - xl)
    (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ p ∈ coordinateRectangle radius lo hi, s0 ≤ S p)
    (hcoeff : ∀ p ∈ coordinateRectangle radius lo hi,
      |bTheta p| ≤ M ∧ |bXi p| ≤ M ∧ |coordPartial 0 P p| ≤ M ∧
        |coordPartial 0 S p| ≤ M ∧ |coordPartial 1 S p| ≤ M)
    (hchar : ∀ p ∈ coordinateRectangle radius lo hi, |P p| + Real.sqrt (S p) ≤ speed)
    (hEq : ∀ p ∈ coordinateRectangle radius lo hi, hyperbolicOperator P S v p =
      bTheta p * coordPartial 1 v p + bXi p * coordPartial 0 v p + R p) :
    Real.sqrt (movingEnergy xl xr a speed S v b) ≤
      Real.exp ((8 * M * (1 + 1 / s0)) * (b - a)) *
        (Real.sqrt (∫ xi in xl..xr, energyDensity S v (coordinatePoint xi a)) +
          ∫ t in a..b, movingSourceNorm xl xr a speed R t) := by
  have htime : Icc a b ⊆ Ioo lo hi :=
    fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  have hgeo (t : ℝ) (ht : t ∈ Icc a b) :=
    inward_interval_geometry hab hspeed hxl hxr hlength ht
  have hleft (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).1
  have hright (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).2.1
  have horder (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).2.2.1.le
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (movingEnergy xl xr a speed S v)
        (movingEnergyRate xl xr a speed P S bTheta bXi v R t) t :=
    movingEnergy_hasDerivAt hP hS hbt hbx hv hR hradius
      (hleft t ht) (hright t ht) (htime ht) hEq
  have hEcont : ContinuousOn (movingEnergy xl xr a speed S v) (Icc a b) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hEpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ movingEnergy xl xr a speed S v t := by
    apply movingEnergy_nonneg (horder t ht)
    intro x hx
    apply hs0.le.trans (hSfloor _ _)
    exact point_mem_rectangle
      ⟨(hleft t ht).1.trans_le hx.1, hx.2.trans_lt (hright t ht).2⟩ (htime ht)
  have hforce := movingSourceNorm_continuousOn hR hradius hleft hright htime
  have hC : 0 ≤ 8 * M * (1 + 1 / s0) := by positivity
  have hbound (t : ℝ) (ht : t ∈ Ioo a b) :
      movingEnergyRate xl xr a speed P S bTheta bXi v R t ≤
        (8 * M * (1 + 1 / s0)) * movingEnergy xl xr a speed S v t +
          Real.sqrt (2 * movingEnergy xl xr a speed S v t) * movingSourceNorm xl xr a speed R t :=
    movingEnergyRate_le hP hS hbt hbx hv hR
      (hleft t ⟨ht.1.le, ht.2.le⟩) (hright t ⟨ht.1.le, ht.2.le⟩)
      (htime ⟨ht.1.le, ht.2.le⟩) (horder t ⟨ht.1.le, ht.2.le⟩)
      hs0 hM hSfloor hcoeff hchar
  have hfinal := sqrt_energy_gronwall hab hEcont
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩) hEpos hforce
    (fun t _ => Real.sqrt_nonneg _) hC hbound
  simpa only [movingEnergy, movingIntervalIntegral, inwardLeft, inwardRight,
    sub_self, mul_zero, add_zero, sub_zero] using hfinal

end SmoothLocal.Hyperbolic

end

end OAI
