import OAI.Geometry.IsometricImmersion.Caps.CapAreaFormula

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem exists_actual_cap_area_chart
    {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      e.source = pairRectangle 2 (-2) 2 ∧
      e.target = triangularFlow Y '' pairRectangle 2 (-2) 2 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ capChartDomain,
        (fderiv ℝ (capChart Y) p).det = coordPartial 1 (capFlowHeight Y) p ∧
        Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M)) ∧
      ∀ tl tr sb st : ℝ, tl ≤ tr → sb ≤ st →
        closedRectangle tl tr sb st ⊆ capChartDomain → ∀ f : Coord → ℝ,
        ContinuousOn f (capChart Y '' closedRectangle tl tr sb st) →
        (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) =
          rectangleIntegral tl tr sb st (fun p => coordPartial 1 (capFlowHeight Y) p*capPullback Y f p) ∧
        Real.exp (-2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
          (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) ∧
        (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) ≤
          Real.exp (2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ∧
        rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
          Real.exp (2*M)*(∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) := by
  obtain ⟨e,hsource,htarget,heq,hforward,hinverse⟩ :=
    exists_global_triangularFlow_chart hq hU hSU hY hrange hstart hode
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s :=
    fun s hs t ht => cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht
  have hJ (p : Coord) (hp : p ∈ capChartDomain) :=
    capChart_jacobian_bounds hq hU hSU hY hrange hstart hode hM hMq hp
  refine ⟨e,hsource,htarget,heq,hforward,hinverse,?_,?_⟩
  · intro p hp
    exact ⟨capChart_det_fderiv hYs hp,hJ p hp⟩
  · intro tl tr sb st ht hs hbox f hf
    have hJrect := fun p (hp : p ∈ closedRectangle tl tr sb st) => hJ p (hbox hp)
    obtain ⟨hlower,hupper⟩ := cap_rectangle_square_integral_bounds hYs hvar hsource heq ht hs hbox hJrect hf
    exact ⟨cap_image_integral_formula hYs hvar hsource heq ht hs hbox hf,
      hlower,hupper,cap_pullback_square_integral_le_image hYs hvar hsource heq ht hs hbox hJrect hf⟩

theorem constructed_cap_pullback_square_le_region
    {q : Coord → ℝ} {U V : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st))
    (himage : capChart Y '' closedRectangle tl tr sb st ⊆ V)
    (hLp : MemLp f 2 (volume.restrict V)) :
    rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
      Real.exp (2*M)*(∫ p in V, (f p)^2) := by
  obtain ⟨e,hsource,htarget,heq,hforward,hinverse,hJ,hbridge⟩ :=
    exists_actual_cap_area_chart hq hU hSU hY hrange hstart hode hM hMq
  have hcomp := (hbridge tl tr sb st ht hs hbox f hf).2.2.2
  have hregion : (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) ≤
      ∫ p in V, (f p)^2 :=
    setIntegral_mono_set hLp.integrable_sq (Filter.Eventually.of_forall (fun p => sq_nonneg (f p)))
      himage.eventuallyLE
  exact hcomp.trans (mul_le_mul_of_nonneg_left hregion (Real.exp_pos _).le)

end SmoothLocal.Flow

end

end OAI
