import OAI.Geometry.IsometricImmersion.Caps.ConstructedCapArea
import OAI.Geometry.IsometricImmersion.Caps.CapGradientTransport

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capChart_mapsTo_modelSquare_of_range {Y : ℝ → ℝ → ℝ}
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3) :
    MapsTo (capChart Y) capChartDomain modelSquare := by
  intro p hp
  apply coordinatePoint_mem_modelSquare
  · exact ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
  · exact hrange (p 1) ⟨hp.2.1.le,hp.2.2.le⟩ (p 0) ⟨hp.1.1.le,hp.1.2.le⟩

theorem coordinate_partial_sq_le_gradient (f : Coord → ℝ) (p : Coord) (i : Fin 2) :
    (coordPartial i f p)^2 ≤ coordinateGradientSquare f p := by
  fin_cases i <;> simp only [Fin.mk_zero,Fin.mk_one,coordinateGradientSquare]
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · exact le_add_of_nonneg_left (sq_nonneg _)

theorem cap_image_partial_square_le_gradient
    {Y : ℝ → ℝ → ℝ} {f : Coord → ℝ} {U : Set Coord}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    {tl tr sb st : ℝ} (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (i : Fin 2) :
    (∫ p in capChart Y '' closedRectangle tl tr sb st, (coordPartial i f p)^2) ≤
      ∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p := by
  have hc : IsCompact (capChart Y '' closedRectangle tl tr sb st) :=
    (capRectangle_isCompact _ _ _ _).image_of_continuousOn
      ((capChart_contDiffOn hYs).continuousOn.mono hbox)
  have hsub : capChart Y '' closedRectangle tl tr sb st ⊆ U := by
    rintro _ ⟨p,hp,rfl⟩
    exact hmap (hbox hp)
  have hi : ContinuousOn (fun p => (coordPartial i f p)^2)
      (capChart Y '' closedRectangle tl tr sb st) :=
    ((partial_contDiffOn hf hU i).continuousOn.mono hsub).pow 2
  have hg : ContinuousOn (coordinateGradientSquare f)
      (capChart Y '' closedRectangle tl tr sb st) :=
    (coordinateGradientSquare_contDiffOn hf hU).continuousOn.mono hsub
  exact setIntegral_mono_on (hi.integrableOn_compact hc) (hg.integrableOn_compact hc)
    hc.isClosed.measurableSet (fun p _hp => coordinate_partial_sq_le_gradient f p i)

theorem constructed_cap_gradient_integral_bounds
    {q f : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U)
    {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) ≤
      ((2+(Real.exp (2*M))^2)*Real.exp (2*M))*
        (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ≤
      (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*
        rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) ∧
    ∀ i : Fin 2,
      (∫ p in capChart Y '' closedRectangle tl tr sb st, (coordPartial i f p)^2) ≤
        (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*
          rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) := by
  obtain ⟨e,hsource,htarget,heq,hforward,hinverse⟩ :=
    exists_global_triangularFlow_chart hq hU hSU hY hrange hstart hode
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s :=
    fun s hs t ht => cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht
  have hmapS := capChart_mapsTo_modelSquare_of_range hrange
  have hmap : MapsTo (capChart Y) capChartDomain U := fun _ hp => hSU (hmapS hp)
  have hJ := fun p (hp : p ∈ closedRectangle tl tr sb st) =>
    capChart_jacobian_bounds hq hU hSU hY hrange hstart hode hM hMq (hbox hp)
  obtain ⟨hfwd,hinv⟩ := cap_gradient_integral_bounds hYs hvar hode hsource heq hf hU hmap ht hs hbox
    (fun p hp => hq0 _ (hmapS (hbox hp))) hJ
  refine ⟨hfwd,hinv,?_⟩
  intro i
  exact (cap_image_partial_square_le_gradient hYs hf hU hmap hbox i).trans hinv

end SmoothLocal.Flow

end

end OAI
