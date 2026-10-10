import OAI.Geometry.IsometricImmersion.Caps.CapJacobian
import OAI.Geometry.IsometricImmersion.Energy.RegionSobolev
import OAI.Geometry.IsometricImmersion.Caps.EllipticGradient

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem capRectangle_isCompact (tl tr sb st : ℝ) : IsCompact (closedRectangle tl tr sb st) := by
  have he : closedRectangle tl tr sb st =
      (fun q : ℝ × ℝ => boxPoint q.1 q.2) '' (Icc tl tr ×ˢ Icc sb st) := by
    ext p
    constructor
    · intro hp
      exact ⟨(p 0,p 1),⟨hp.1,hp.2⟩,boxPoint_eta p⟩
    · rintro ⟨q,hq,rfl⟩
      exact boxPoint_mem hq.1 hq.2
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image (by unfold boxPoint; fun_prop)

theorem rectangleIntegral_eq_coordinate_closed_area
    {tl tr sb st : ℝ} {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F = ∫ p in closedRectangle tl tr sb st, F p := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hh := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding
    (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) (Icc tl tr ×ˢ Icc sb st)
  change (∫ p in closedRectangle tl tr sb st, F (boxPoint (p 0) (p 1))) =
    ∫ q in Icc tl tr ×ˢ Icc sb st, F (boxPoint q.1 q.2) at hh
  simpa only [boxPoint_eta] using hh.symm

theorem cap_image_integral_formula
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) =
      rectangleIntegral tl tr sb st (fun p => coordPartial 1 (capFlowHeight Y) p*capPullback Y f p) := by
  have hrect : MeasurableSet (closedRectangle tl tr sb st) := (capRectangle_isCompact _ _ _ _).isClosed.measurableSet
  have hchart := capChart_contDiffOn hYs
  have hd (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      HasFDerivWithinAt (capChart Y) (fderiv ℝ (capChart Y) p) (closedRectangle tl tr sb st) p :=
    ((hchart.contDiffAt (capChartDomain_isOpen.mem_nhds (hbox hp))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj := (capChart_injOn_of_pairChart hsource heq).mono hbox
  have hcomp : ContinuousOn (capPullback Y f) (closedRectangle tl tr sb st) :=
    hf.comp (hchart.continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)
  have hJ : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  calc
    _ = ∫ p in closedRectangle tl tr sb st, |(fderiv ℝ (capChart Y) p).det| • f (capChart Y p) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hrect hd hinj f
    _ = ∫ p in closedRectangle tl tr sb st, coordPartial 1 (capFlowHeight Y) p*capPullback Y f p := by
      apply setIntegral_congr_fun hrect
      intro p hp
      change |(fderiv ℝ (capChart Y) p).det| * f (capChart Y p) = _
      rw [capChart_abs_det_fderiv hYs hvar (hbox hp)]
      rfl
    _ = _ := (rectangleIntegral_eq_coordinate_closed_area ht hs (hJ.mul hcomp)).symm

theorem cap_rectangle_square_integral_bounds
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
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    Real.exp (-2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
      ∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2 ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) ≤
      Real.exp (2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) := by
  have hchart := capChart_contDiffOn hYs
  have hfc : ContinuousOn (fun p => (capPullback Y f p)^2) (closedRectangle tl tr sb st) :=
    (hf.comp (hchart.continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)).pow 2
  have hJc : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  have hformula := cap_image_integral_formula hYs hvar hsource heq ht hs hbox (hf.pow 2)
  change (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) =
    rectangleIntegral tl tr sb st (fun p => coordPartial 1 (capFlowHeight Y) p*(capPullback Y f p)^2) at hformula
  rw [hformula]
  constructor
  · have hh := rectangleIntegral_mono ht hs (continuousOn_const.mul hfc) (hJc.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).1 (sq_nonneg _))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh
  · have hh := rectangleIntegral_mono ht hs (hJc.mul hfc) (continuousOn_const.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).2 (sq_nonneg _))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh

theorem cap_pullback_square_integral_le_image
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
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
      Real.exp (2*M)*(∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) := by
  have hh := (cap_rectangle_square_integral_bounds hYs hvar hsource heq ht hs hbox hJ hf).1
  have hscale : Real.exp (2*M)*Real.exp (-2*M) = 1 := by rw [←Real.exp_add]; simp
  calc
    _ = Real.exp (2*M)*(Real.exp (-2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2)) := by
      rw [←mul_assoc,hscale,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

end SmoothLocal.Flow

end

end OAI
