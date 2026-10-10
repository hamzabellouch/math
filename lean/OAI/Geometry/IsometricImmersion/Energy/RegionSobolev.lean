import OAI.Geometry.IsometricImmersion.Energy.RectangleSobolev
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

def halfOpenCoordinateRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioc tl tr ∧ p 1 ∈ Ioc sb st}

theorem boxPoint_eta (p : Coord) : boxPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [boxPoint]

theorem rectangleIntegral_eq_coordinate_area
    {tl tr sb st : ℝ} {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F = ∫ p in halfOpenCoordinateRectangle tl tr sb st, F p := by
  rw [rectangleIntegral_eq_area ht hs hF]
  have h := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding
    (fun p : ℝ × ℝ => F (boxPoint p.1 p.2)) (Ioc tl tr ×ˢ Ioc sb st)
  change (∫ p in halfOpenCoordinateRectangle tl tr sb st, F (boxPoint (p 0) (p 1))) =
    ∫ p in Ioc tl tr ×ˢ Ioc sb st, F (boxPoint p.1 p.2) at h
  simpa only [boxPoint_eta] using h.symm

theorem rectangle_square_integral_le_region
    {tl tr sb st : ℝ} {f : Coord → ℝ} {V : Set Coord}
    (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st))
    (hsub : closedRectangle tl tr sb st ⊆ V) (hLp : MemLp f 2 (volume.restrict V)) :
    rectangleIntegral tl tr sb st (fun p => f p ^ 2) ≤ ∫ p in V, f p ^ 2 := by
  have hfsq : ContinuousOn (fun p => f p^2) (closedRectangle tl tr sb st) := hf.pow 2
  rw [rectangleIntegral_eq_coordinate_area ht hs hfsq]
  have hhalf : halfOpenCoordinateRectangle tl tr sb st ⊆ V := by
    intro p hp
    exact hsub ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
  exact setIntegral_mono_set hLp.integrable_sq
    (Filter.Eventually.of_forall (fun p => sq_nonneg (f p))) hhalf.eventuallyLE

def squareSobolevWeight (r : ℝ) : ℝ := 1 + 1 / (2 * r)

def regionSobolevEnergy (r : ℝ) (V : Set Coord) (f : Coord → ℝ) : ℝ :=
  squareSobolevWeight r * squareSobolevWeight r * (∫ p in V, f p ^ 2) +
  squareSobolevWeight r * (∫ p in V, coordPartial 0 f p ^ 2) +
  squareSobolevWeight r * (∫ p in V, coordPartial 1 f p ^ 2) +
  ∫ p in V, coordPartial 1 (coordPartial 0 f) p ^ 2

theorem point_square_bound_on_region
    {f : Coord → ℝ} {U V : Set Coord} {p : Coord} {r : ℝ} (hr : 0 < r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hVU : V ⊆ U)
    (hsquare : closedRectangle (p 0 - r) (p 0 + r) (p 1 - r) (p 1 + r) ⊆ V)
    (h0 : MemLp f 2 (volume.restrict V))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict V))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict V))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2 (volume.restrict V)) :
    f p ^ 2 ≤ regionSobolevEnergy r V f := by
  have ht : p 0 - r < p 0 + r := by linarith
  have hs : p 1 - r < p 1 + r := by linarith
  have hbox := hsquare.trans hVU
  have hfx := partial_contDiffOn hf hU 0
  have hfy := partial_contDiffOn hf hU 1
  have hfyx := partial_contDiffOn hfx hU 1
  have hSob := rectangle_point_square_bound ht hs hU hf hbox
    (x := p 0) (y := p 1) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hw : 0 ≤ squareSobolevWeight r := by
    unfold squareSobolevWeight
    exact add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  have hE0 := rectangle_square_integral_le_region ht.le hs.le (hf.continuousOn.mono hbox) hsquare h0
  have hEx := rectangle_square_integral_le_region ht.le hs.le (hfx.continuousOn.mono hbox) hsquare hx
  have hEy := rectangle_square_integral_le_region ht.le hs.le (hfy.continuousOn.mono hbox) hsquare hy
  have hExy := rectangle_square_integral_le_region ht.le hs.le (hfyx.continuousOn.mono hbox) hsquare hxy
  have hwidth0 : (p 0 + r) - (p 0 - r) = 2 * r := by ring
  have hwidth1 : (p 1 + r) - (p 1 - r) = 2 * r := by ring
  rw [boxPoint_eta, hwidth0, hwidth1] at hSob
  change f p ^ 2 ≤ squareSobolevWeight r * squareSobolevWeight r * _ +
    squareSobolevWeight r * _ + squareSobolevWeight r * _ + _ at hSob
  exact hSob.trans (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hE0 (mul_nonneg hw hw))
      (mul_le_mul_of_nonneg_left hEx hw))
    (mul_le_mul_of_nonneg_left hEy hw)) hExy)

theorem point_abs_bound_on_region
    {f : Coord → ℝ} {U V : Set Coord} {p : Coord} {r : ℝ} (hr : 0 < r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hVU : V ⊆ U)
    (hsquare : closedRectangle (p 0 - r) (p 0 + r) (p 1 - r) (p 1 + r) ⊆ V)
    (h0 : MemLp f 2 (volume.restrict V))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict V))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict V))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2 (volume.restrict V)) :
    |f p| ≤ Real.sqrt (regionSobolevEnergy r V f) := by
  have h := point_square_bound_on_region hr hU hf hVU hsquare h0 hx hy hxy
  have he : 0 ≤ regionSobolevEnergy r V f := (sq_nonneg _).trans h
  nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (regionSobolevEnergy r V f), sq_abs (f p), abs_nonneg (f p)]

end SmoothLocal.Sobolev

end

end OAI
