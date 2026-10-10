import OAI.Geometry.IsometricImmersion.Caps.CapAreaFormula

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem cap_rectangle_density_integral_bounds
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st))
    (hf0 : ∀ p ∈ capChart Y '' closedRectangle tl tr sb st, 0 ≤ f p) :
    Real.exp (-2*M)*rectangleIntegral tl tr sb st (capPullback Y f) ≤
      (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) ≤
      Real.exp (2*M)*rectangleIntegral tl tr sb st (capPullback Y f) := by
  have hfc : ContinuousOn (capPullback Y f) (closedRectangle tl tr sb st) :=
    hf.comp ((capChart_contDiffOn hYs).continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)
  have hJc : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  rw [cap_image_integral_formula hYs hvar hsource heq ht hs hbox hf]
  constructor
  · have hh := rectangleIntegral_mono ht hs (continuousOn_const.mul hfc) (hJc.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).1 (hf0 _ ⟨p,hp,rfl⟩))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh
  · have hh := rectangleIntegral_mono ht hs (hJc.mul hfc) (continuousOn_const.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).2 (hf0 _ ⟨p,hp,rfl⟩))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh

theorem cap_pullback_density_integral_le_image
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st))
    (hf0 : ∀ p ∈ capChart Y '' closedRectangle tl tr sb st, 0 ≤ f p) :
    rectangleIntegral tl tr sb st (capPullback Y f) ≤
      Real.exp (2*M)*(∫ p in capChart Y '' closedRectangle tl tr sb st, f p) := by
  have hh := (cap_rectangle_density_integral_bounds hYs hvar hsource heq ht hs hbox hJ hf hf0).1
  have hscale : Real.exp (2*M)*Real.exp (-2*M) = 1 := by
    rw [←Real.exp_add,show 2*M+(-2*M) = 0 by ring,Real.exp_zero]
  calc
    _ = Real.exp (2*M)*(Real.exp (-2*M)*rectangleIntegral tl tr sb st (capPullback Y f)) := by
      rw [←mul_assoc,hscale,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

end SmoothLocal.Flow

end

end OAI
