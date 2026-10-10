import OAI.Geometry.IsometricImmersion.Caps.CapDensityBounds

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def coordinateGradientSquare (f : Coord → ℝ) (p : Coord) : ℝ :=
  (coordPartial 0 f p)^2+(coordPartial 1 f p)^2

theorem coordinateGradientSquare_nonneg (f : Coord → ℝ) (p : Coord) :
    0 ≤ coordinateGradientSquare f p := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem coordinateGradientSquare_contDiffOn {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) :
    ContDiffOn ℝ ∞ (coordinateGradientSquare f) V :=
  ((partial_contDiffOn hf hV 0).pow 2).add ((partial_contDiffOn hf hV 1).pow 2)

theorem triangular_gradient_forward_scalar {a b H x y : ℝ}
    (ha : |a| ≤ 1) (hb : 0 ≤ b) (hbH : b ≤ H) :
    (x+a*y)^2+(b*y)^2 ≤ (2+H^2)*(x^2+y^2) := by
  have hH : 0 ≤ H := hb.trans hbH
  have ha2 : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hb2 : b^2 ≤ H^2 := (sq_le_sq₀ hb hH).2 hbH
  have hay := mul_le_mul_of_nonneg_right ha2 (sq_nonneg y)
  have hby := mul_le_mul_of_nonneg_right hb2 (sq_nonneg y)
  have hsum : (x+a*y)^2 ≤ 2*(x^2+(a*y)^2) := add_sq_le
  have hx := mul_nonneg (sq_nonneg H) (sq_nonneg x)
  nlinarith only [hay,hby,hsum,hx]

theorem triangular_gradient_inverse_scalar {a b H x y : ℝ}
    (ha : |a| ≤ 1) (hH : 0 < H) (hb : 1/H ≤ b) :
    x^2+y^2 ≤ (2+3*H^2)*((x+a*y)^2+(b*y)^2) := by
  have ha2 : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hHb : 1 ≤ b*H := (div_le_iff₀ hH).1 hb
  have hHb2 : 1 ≤ (b*H)^2 := by
    simpa only [one_pow] using (sq_le_sq₀ (show (0:ℝ) ≤ 1 by norm_num) (by linarith : 0 ≤ b*H)).2 hHb
  have hy := mul_le_mul_of_nonneg_right hHb2 (sq_nonneg y)
  have hay := mul_le_mul_of_nonneg_right ha2 (sq_nonneg y)
  have hx : ((x+a*y)+(-a*y))^2 ≤ 2*((x+a*y)^2+(-a*y)^2) := add_sq_le
  have hgap : 0 ≤ 3*H^2*(x+a*y)^2+2*(b*y)^2 := by positivity
  nlinarith only [hy,hay,hx,hgap]

theorem capPullback_gradient_pointwise
    {Y : ℝ → ℝ → ℝ} {q f : Coord → ℝ} {M : ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hf : DifferentiableAt ℝ f (capChart Y p))
    (hq : |q (capChart Y p)| ≤ 1)
    (hJ : Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
      coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M)) :
    coordinateGradientSquare (capPullback Y f) p ≤
      (2+(Real.exp (2*M))^2)*capPullback Y (coordinateGradientSquare f) p ∧
    capPullback Y (coordinateGradientSquare f) p ≤
      (2+3*(Real.exp (2*M))^2)*coordinateGradientSquare (capPullback Y f) p := by
  have hJpos : 0 < coordPartial 1 (capFlowHeight Y) p := (Real.exp_pos _).trans_le hJ.1
  have hJinv : 1/Real.exp (2*M) ≤ coordPartial 1 (capFlowHeight Y) p := by
    simpa only [show -2*M = -(2*M) by ring,Real.exp_neg,one_div] using hJ.1
  have htime := capPullback_partial_time hYs hode hp hf
  have hinit := capPullback_partial_initial hYs hp hf
  change (coordPartial 0 (capPullback Y f) p)^2+(coordPartial 1 (capPullback Y f) p)^2 ≤
      (2+(Real.exp (2*M))^2)*((coordPartial 0 f (capChart Y p))^2+(coordPartial 1 f (capChart Y p))^2) ∧
    (coordPartial 0 f (capChart Y p))^2+(coordPartial 1 f (capChart Y p))^2 ≤
      (2+3*(Real.exp (2*M))^2)*((coordPartial 0 (capPullback Y f) p)^2+(coordPartial 1 (capPullback Y f) p)^2)
  rw [htime,hinit]
  simp only [coordinateDrift,capPullback]
  have ha : |-q (capChart Y p)| ≤ 1 := by simpa only [abs_neg] using hq
  constructor
  · simpa only [neg_mul,sub_eq_add_neg,mul_comm] using
      triangular_gradient_forward_scalar (x := coordPartial 0 f (capChart Y p))
        (y := coordPartial 1 f (capChart Y p)) ha hJpos.le hJ.2
  · simpa only [neg_mul,sub_eq_add_neg,mul_comm] using
      triangular_gradient_inverse_scalar (x := coordPartial 0 f (capChart Y p))
        (y := coordPartial 1 f (capChart Y p)) ha (Real.exp_pos _) hJinv

theorem cap_gradient_integral_bounds
    {Y : ℝ → ℝ → ℝ} {q f : Coord → ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V)
    (hmap : MapsTo (capChart Y) capChartDomain V)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hq : ∀ p ∈ closedRectangle tl tr sb st, |q (capChart Y p)| ≤ 1)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M)) :
    rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) ≤
      ((2+(Real.exp (2*M))^2)*Real.exp (2*M))*
        (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ≤
      (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*
        rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) := by
  have hGp := coordinateGradientSquare_contDiffOn hf hV
  have hGc : ContinuousOn (coordinateGradientSquare f) (capChart Y '' closedRectangle tl tr sb st) :=
    hGp.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmap (hbox hp))
  have hP : ContDiffOn ℝ ∞ (capPullback Y f) capChartDomain := capPullback_contDiffOn hYs hf hmap
  have hGPc : ContinuousOn (coordinateGradientSquare (capPullback Y f)) (closedRectangle tl tr sb st) :=
    (coordinateGradientSquare_contDiffOn hP capChartDomain_isOpen).continuousOn.mono hbox
  have hPGc : ContinuousOn (capPullback Y (coordinateGradientSquare f)) (closedRectangle tl tr sb st) :=
    (capPullback_contDiffOn hYs hGp hmap).continuousOn.mono hbox
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :=
    capPullback_gradient_pointwise hYs hode (hbox hp)
      ((hf.contDiffAt (hV.mem_nhds (hmap (hbox hp)))).differentiableAt (by simp)) (hq p hp) (hJ p hp)
  have hzero := fun p (_hp : p ∈ capChart Y '' closedRectangle tl tr sb st) =>
    coordinateGradientSquare_nonneg f p
  have hforward := rectangleIntegral_mono ht hs hGPc (continuousOn_const.mul hPGc)
    (fun p hp => (hpoint p hp).1)
  simp only [Pi.mul_def, rectangleIntegral_const_mul] at hforward
  have hinverse := rectangleIntegral_mono ht hs hPGc (continuousOn_const.mul hGPc)
    (fun p hp => (hpoint p hp).2)
  simp only [Pi.mul_def, rectangleIntegral_const_mul] at hinverse
  have hlower := cap_pullback_density_integral_le_image hYs hvar hsource heq ht hs hbox hJ hGc hzero
  have hupper := (cap_rectangle_density_integral_bounds hYs hvar hsource heq ht hs hbox hJ hGc hzero).2
  constructor
  · calc
      _ ≤ (2+(Real.exp (2*M))^2)*rectangleIntegral tl tr sb st
          (capPullback Y (coordinateGradientSquare f)) := hforward
      _ ≤ (2+(Real.exp (2*M))^2)*(Real.exp (2*M)*
          (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p)) :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ Real.exp (2*M)*rectangleIntegral tl tr sb st
          (capPullback Y (coordinateGradientSquare f)) := hupper
      _ ≤ Real.exp (2*M)*((2+3*(Real.exp (2*M))^2)*
          rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f))) :=
        mul_le_mul_of_nonneg_left hinverse (Real.exp_pos _).le
      _ = _ := by ring

end SmoothLocal.Flow

end

end OAI
