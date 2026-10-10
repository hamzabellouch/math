import OAI.Geometry.IsometricImmersion.Flows.FlowImageFirstBounds
import OAI.Geometry.IsometricImmersion.Flows.FlowCurvature
import OAI.Geometry.IsometricImmersion.Energy.RectangleSobolev
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def openCoordinateRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioo tl tr ∧ p 1 ∈ Ioo sb st}

def flowInteriorRadius (M dt ds : ℝ) : ℝ :=
  min (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)

theorem flowInteriorRadius_pos (M : ℝ) {dt ds : ℝ} (ht : 0 < dt) (hs : 0 < ds) :
    0 < flowInteriorRadius M dt ds := by
  apply lt_min
  · exact half_pos ht
  · exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hs

theorem flowInteriorRadius_lt_time (M : ℝ) {dt ds : ℝ} (ht : 0 < dt) :
    flowInteriorRadius M dt ds < dt := by
  have h := min_le_left (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)
  change flowInteriorRadius M dt ds ≤ dt / 2 at h
  linarith

theorem flowInteriorRadius_vertical_margin (M : ℝ) {dt ds : ℝ} (hs : 0 < ds) :
    ((101 : ℝ) / 100) * flowInteriorRadius M dt ds < Real.exp (-2 * M) * ds := by
  have h := min_le_right (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)
  change flowInteriorRadius M dt ds ≤ ((50 : ℝ) / 101) * Real.exp (-2 * M) * ds at h
  have hp := mul_pos (Real.exp_pos (-2 * M)) hs
  nlinarith

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem actual_flow_ordinary_rectangle_inclusion
    {M tl tr sb st dt ds t0 s0 : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds)
    (ht0 : t0 ∈ Icc (tl + dt) (tr - dt))
    (hs0 : s0 ∈ Icc (sb + ds) (st - ds)) :
    closedRectangle (t0 - flowInteriorRadius M dt ds) (t0 + flowInteriorRadius M dt ds)
      (Y s0 t0 - flowInteriorRadius M dt ds) (Y s0 t0 + flowInteriorRadius M dt ds) ⊆
      capChart Y '' openCoordinateRectangle tl tr sb st := by
  intro p hp
  let r := flowInteriorRadius M dt ds
  have hr : 0 < r := flowInteriorRadius_pos M hdt hds
  have hrt : r < dt := flowInteriorRadius_lt_time M hdt
  have hrs : ((101 : ℝ) / 100) * r < Real.exp (-2 * M) * ds :=
    flowInteriorRadius_vertical_margin M hds
  have hpx : p 0 ∈ Icc (t0 - r) (t0 + r) := hp.1
  have hpy : p 1 ∈ Icc (Y s0 t0 - r) (Y s0 t0 + r) := hp.2
  have htime : p 0 ∈ Ioo tl tr := by constructor <;> linarith [ht0.1, ht0.2, hpx.1, hpx.2]
  have htimeGlobal : p 0 ∈ Ioo (-2 : ℝ) 2 := ⟨htl.trans htime.1, htime.2.trans htr⟩
  have ht0Global : t0 ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [ht0.1, ht0.2]
  have hs0Global : s0 ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hsbGlobal : sb ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hstGlobal : st ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hsb0 : sb ≤ s0 := by linarith [hs0.1]
  have hs0t : s0 ≤ st := by linarith [hs0.2]
  have hlow := cap_flow_seed_gap hq hU hSU hY hrange hstart hode hM hq1
    hsbGlobal hs0Global htimeGlobal hsb0
  have hupp := cap_flow_seed_gap hq hU hSU hY hrange hstart hode hM hq1
    hs0Global hstGlobal htimeGlobal hs0t
  have hgap0 : Real.exp (-2 * M) * ds ≤ Real.exp (-2 * M) * (s0 - sb) :=
    mul_le_mul_of_nonneg_left (by linarith [hs0.1]) (Real.exp_pos _).le
  have hgap1 : Real.exp (-2 * M) * ds ≤ Real.exp (-2 * M) * (st - s0) :=
    mul_le_mul_of_nonneg_left (by linarith [hs0.2]) (Real.exp_pos _).le
  have hxdist : |p 0 - t0| ≤ r := abs_le.mpr ⟨by linarith [hpx.1], by linarith [hpx.2]⟩
  have hmove : |Y s0 (p 0) - Y s0 t0| ≤ ((1 : ℝ) / 100) * r :=
    (cap_flow_time_lipschitz hq hU hSU hY hrange hstart hode hq0
      hs0Global ht0Global htimeGlobal).trans
      (mul_le_mul_of_nonneg_left hxdist (by norm_num))
  have hlo : Y sb (p 0) < p 1 := by
    have hm := (abs_le.mp hmove).2
    nlinarith [hlow, hgap0, hpy.1, hrs]
  have hhi : p 1 < Y st (p 0) := by
    have hm := (abs_le.mp hmove).1
    nlinarith [hupp, hgap1, hpy.2, hrs]
  have hsb_st : sb ≤ st := hsb0.trans hs0t
  have hseedCont : ContinuousOn (fun s : ℝ => (s, p 0)) (Icc sb st) := by fun_prop
  have hseedMap : MapsTo (fun s : ℝ => (s, p 0)) (Icc sb st)
      (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    intro s hs
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨htimeGlobal.1.le, htimeGlobal.2.le⟩⟩
  have hcont : ContinuousOn (fun s => Y s (p 0)) (Icc sb st) := by
    convert hY.comp hseedCont hseedMap using 1; rfl
  obtain ⟨s, hs, hse⟩ := intermediate_value_Icc hsb_st hcont ⟨hlo.le, hhi.le⟩
  have hsStrict : s ∈ Ioo sb st := by
    constructor
    · by_contra hnot
      have he : s = sb := le_antisymm (le_of_not_gt hnot) hs.1
      subst s
      linarith
    · by_contra hnot
      have he : s = st := le_antisymm hs.2 (le_of_not_gt hnot)
      subst s
      linarith
  refine ⟨boxPoint (p 0) s, ?_, ?_⟩
  · simpa [openCoordinateRectangle, boxPoint] using And.intro htime hsStrict
  · ext i
    fin_cases i <;> simp [capChart, capFlowHeight, boxPoint, coordinatePoint, hse]

theorem actual_flow_uniform_image_margin
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) :
    0 < flowInteriorRadius M dt ds ∧
      ∀ p ∈ capChart Y '' closedRectangle (tl + dt) (tr - dt) (sb + ds) (st - ds),
        closedRectangle (p 0 - flowInteriorRadius M dt ds) (p 0 + flowInteriorRadius M dt ds)
          (p 1 - flowInteriorRadius M dt ds) (p 1 + flowInteriorRadius M dt ds) ⊆
          capChart Y '' openCoordinateRectangle tl tr sb st := by
  refine ⟨flowInteriorRadius_pos M hdt hds, ?_⟩
  rintro p ⟨a, ha, rfl⟩
  simpa [capChart, capFlowHeight, coordinatePoint] using
    actual_flow_ordinary_rectangle_inclusion hq hU hSU hY hrange hstart hode
      hM hq0 hq1 htl htr hsb hst hdt hds ha.1 ha.2

end SmoothLocal.Flow

end

end OAI
