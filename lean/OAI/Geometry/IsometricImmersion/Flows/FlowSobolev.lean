import OAI.Geometry.IsometricImmersion.Flows.FlowImageMargin
import OAI.Geometry.IsometricImmersion.Energy.RegionSobolev

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem openCoordinateRectangle_subset_closed (tl tr sb st : ℝ) :
    openCoordinateRectangle tl tr sb st ⊆ closedRectangle tl tr sb st := by
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩

variable {q f : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)

include hSU hrange

theorem actual_closed_flow_rectangle_subset_domain
    {tl tr sb st : ℝ} (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2) :
    capChart Y '' closedRectangle tl tr sb st ⊆ U := by
  rintro p ⟨a, ha, rfl⟩
  apply hSU
  apply coordinatePoint_mem_modelSquare
  · exact ⟨by linarith [ha.1.1], by linarith [ha.1.2]⟩
  · exact hrange (a 1) ⟨by linarith [ha.2.1], by linarith [ha.2.2]⟩
      (a 0) ⟨by linarith [ha.1.1], by linarith [ha.1.2]⟩

include hq hU hY hstart hode

theorem actual_flow_interior_sobolev
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) (hf : ContDiffOn ℝ ∞ f U)
    (h0 : MemLp f 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2
      (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    {p : Coord}
    (hp : p ∈ capChart Y '' closedRectangle (tl + dt) (tr - dt) (sb + ds) (st - ds)) :
    |f p| ≤ Real.sqrt (regionSobolevEnergy (flowInteriorRadius M dt ds)
      (capChart Y '' closedRectangle tl tr sb st) f) := by
  obtain ⟨hr, hmargin⟩ := actual_flow_uniform_image_margin hq hU hSU hY hrange hstart hode
    hM hq0 hq1 htl htr hsb hst hdt hds
  have hsquare := (hmargin p hp).trans (Set.image_mono
    (openCoordinateRectangle_subset_closed tl tr sb st))
  exact point_abs_bound_on_region hr hU hf
    (actual_closed_flow_rectangle_subset_domain hSU hrange htl htr hsb hst)
    hsquare h0 hx hy hxy

end SmoothLocal.Flow

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry

theorem regionSobolevEnergy_nonneg {r : ℝ} (hr : 0 < r) (V : Set Coord) (f : Coord → ℝ) :
    0 ≤ regionSobolevEnergy r V f := by
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hw hw) (integral_nonneg (fun p => sq_nonneg (f p))))
    (mul_nonneg hw (integral_nonneg (fun p => sq_nonneg (coordPartial 0 f p)))))
    (mul_nonneg hw (integral_nonneg (fun p => sq_nonneg (coordPartial 1 f p)))))
    (integral_nonneg (fun p => sq_nonneg (coordPartial 1 (coordPartial 0 f) p)))

theorem regionSobolevEnergy_le_common_bound
    {r B : ℝ} {V : Set Coord} {f : Coord → ℝ} (hr : 0 < r)
    (h0 : (∫ p in V, f p ^ 2) ≤ B ^ 2)
    (hx : (∫ p in V, coordPartial 0 f p ^ 2) ≤ B ^ 2)
    (hy : (∫ p in V, coordPartial 1 f p ^ 2) ≤ B ^ 2)
    (hxy : (∫ p in V, coordPartial 1 (coordPartial 0 f) p ^ 2) ≤ B ^ 2) :
    regionSobolevEnergy r V f ≤ ((squareSobolevWeight r + 1) * B)^2 := by
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  calc
    regionSobolevEnergy r V f ≤
        squareSobolevWeight r * squareSobolevWeight r * B^2 +
        squareSobolevWeight r * B^2 + squareSobolevWeight r * B^2 + B^2 :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0 (mul_nonneg hw hw))
        (mul_le_mul_of_nonneg_left hx hw)) (mul_le_mul_of_nonneg_left hy hw)) hxy
    _ = _ := by ring

theorem abs_bound_of_regionSobolevEnergy
    {r B : ℝ} {V : Set Coord} {f : Coord → ℝ} {p : Coord}
    (hr : 0 < r) (hB : 0 ≤ B) (hp : |f p| ≤ Real.sqrt (regionSobolevEnergy r V f))
    (h0 : (∫ q in V, f q ^ 2) ≤ B ^ 2)
    (hx : (∫ q in V, coordPartial 0 f q ^ 2) ≤ B ^ 2)
    (hy : (∫ q in V, coordPartial 1 f q ^ 2) ≤ B ^ 2)
    (hxy : (∫ q in V, coordPartial 1 (coordPartial 0 f) q ^ 2) ≤ B ^ 2) :
    |f p| ≤ (squareSobolevWeight r + 1) * B := by
  have hE := regionSobolevEnergy_nonneg hr V f
  have henergy := regionSobolevEnergy_le_common_bound hr h0 hx hy hxy
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  have hbound : 0 ≤ (squareSobolevWeight r + 1) * B := mul_nonneg (by linarith) hB
  have hroot : Real.sqrt (regionSobolevEnergy r V f) ≤ (squareSobolevWeight r + 1) * B := by
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg (regionSobolevEnergy r V f)]
  exact hp.trans hroot

end SmoothLocal.Sobolev

end

end OAI
