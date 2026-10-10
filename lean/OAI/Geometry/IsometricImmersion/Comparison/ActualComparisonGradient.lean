import OAI.Geometry.IsometricImmersion.Metrics.SmoothMetricRestriction
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonGradientSlice

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_comparison_gradient
    {gRef : MetricField} {U S : Set Coord}
    (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField) (P z : Coord → ℝ) (V : Set Coord)
      (boxRadius width pulseRadius a b F : ℝ),
      IsOpen V → V ⊆ U → SmoothPositiveOn g V →
      ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V →
      0 < width → width < boxRadius → a ≤ b →
      closedRectangle (-boxRadius) boxRadius a b ⊆ V →
      closedRectangle (-boxRadius) boxRadius a b ⊆ S →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ‖p‖ ≤ R) →
      CoordinateBound P (closedRectangle (-boxRadius) boxRadius a b) 3 Z0 →
      CoordinateBound z (closedRectangle (-boxRadius) boxRadius a b) 3 Z →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator gRef (qHeightJetSegment P z sigma p)| ∧
          s0 ≤ qFirstCoefficient gRef 5 (qHeightJetSegment P z sigma p)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius, P (boxPoint x a)=z (boxPoint x a)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius,
        coordPartial 1 P (boxPoint x a)=coordPartial 1 z (boxPoint x a)) →
      0 < pulseRadius → 0 ≤ F →
      comparisonEnergySpeed C*(b-a) ≤ width-pulseRadius →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, |metricComparisonSource g gRef P z p| ≤ F) →
      ∀ t ∈ Icc a b, ∀ i : Fin 2,
        Real.sqrt (∫ x in Icc (-pulseRadius) pulseRadius,
          (coordPartial i (comparisonDifference P z) (boxPoint x t))^2) ≤
          Real.sqrt (2*(1+1/s0))*
            (Real.exp (comparisonEnergyRate C Z0 Z s0*(b-a))*F*Real.sqrt (2*width)*(b-a)) := by
  obtain ⟨C,hC,henergy⟩ := exists_actual_comparison_energy hgRef hU hS hSU R Z0 Z hR hc hs0
  refine ⟨C,hC,?_⟩
  intro g P z V boxRadius width pulseRadius a b F hV hVU hg hP hz hw hwR hab
    hboxV hboxS hpB hPZ hzZ hD hxx hmargin hvalue hvelocity hpulse hF hwidth hsource
  let T := closedRectangle (-boxRadius) boxRadius a b
  let speed := comparisonEnergySpeed C
  let rate := comparisonEnergyRate C Z0 Z s0
  have hs : 0 ≤ speed := add_nonneg (zero_le_one.trans hC) (Real.sqrt_nonneg _)
  have hr : 0 ≤ rate := by unfold rate comparisonEnergyRate; positivity
  have hlength : 2*speed*(b-a)<2*width := by linarith
  have hgRefV := hgRef.mono hVU
  have hseg : ∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef V := by
    intro p hp sigma hsigma
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hboxV hp,
      abs_pos.mp (hc.trans_le (hmargin p hp sigma hsigma).1)⟩
  obtain ⟨W,hW,hTW,hWV,_,hWsmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRefV hV hP hz (closedRectangle_compact _ _ _ _) hboxV hseg
  have hSlabT {t : ℝ} (ht : t ∈ Icc a b) : shrinkingSlab (-width) width a t speed ⊆ T := by
    intro p hp
    change p 1 ∈ Icc a t ∧ p 0 ∈ Icc (-width+speed*(p 1-a)) (width-speed*(p 1-a)) at hp
    have hinc : 0 ≤ speed*(p 1-a) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
    exact ⟨⟨by linarith [hp.2.1],
      by linarith [hp.2.2]⟩,⟨hp.1.1,hp.1.2.trans ht.2⟩⟩
  intro t ht i
  have hTT : closedRectangle (-boxRadius) boxRadius a t ⊆ T :=
    fun p hp => ⟨hp.1,⟨hp.2.1,hp.2.2.trans ht.2⟩⟩
  have hlengtht : 2*speed*(t-a)<2*width := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs)
    exact hm.trans_lt hlength
  have hEt := henergy g P z V boxRadius width a t hV hVU hg hP hz hw hwR ht.1
    (hTT.trans hboxV) (hTT.trans hboxS) (fun p hp => hpB p (hTT hp))
    (fun ds hds p hp => hPZ ds hds p (hTT hp)) (fun ds hds p hp => hzZ ds hds p (hTT hp))
    (fun p hp => hD p (hTT hp)) (fun p hp => hxx p (hTT hp))
    (fun p hp sigma hsigma => hmargin p (hTT hp) sigma hsigma) hvalue hvelocity hlengtht
  have horder (s : ℝ) (hsat : s ∈ Icc a t) :
      inwardLeft (-width) a speed s ≤ inwardRight width a speed s := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hsat.2 a) hs
    dsimp [inwardLeft,inwardRight]
    linarith
  have hI := integrated_movingSourceNorm_le_of_pointwise_bound ht.1 hs hF horder
    (fun p hp => hsource p (hSlabT ht hp))
  have hE : Real.sqrt (movingEnergy (-width) width a speed (comparisonCoefficient gRef P z 5)
      (comparisonDifference P z) t) ≤ Real.exp (rate*(b-a))*F*Real.sqrt (2*width)*(b-a) := by
    have hI' : (∫ s in a..t, movingSourceNorm (-width) width a speed
        (metricComparisonSource g gRef P z) s) ≤ F*Real.sqrt (2*width)*(t-a) := by
      simpa only [sub_neg_eq_add,←two_mul] using hI
    have h0 := hEt.trans (mul_le_mul_of_nonneg_left hI' (Real.exp_pos _).le)
    have hexp : Real.exp (rate*(t-a)) ≤ Real.exp (rate*(b-a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hr)
    have htime : F*Real.sqrt (2*width)*(t-a) ≤ F*Real.sqrt (2*width)*(b-a) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (mul_nonneg hF (Real.sqrt_nonneg _))
    have hprod := mul_le_mul hexp htime
      (mul_nonneg (mul_nonneg hF (Real.sqrt_nonneg _)) (sub_nonneg.mpr ht.1)) (Real.exp_pos _).le
    apply h0.trans
    convert hprod using 1
    first | rfl | ring
  have hcover : inwardLeft (-width) a speed t ≤ -pulseRadius ∧
      pulseRadius ≤ inwardRight width a speed t := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hs
    dsimp [inwardLeft,inwardRight]
    constructor <;> linarith
  have hgrad := fixed_slice_gradient_le_moving_energy hW (hWsmooth 5).continuousOn
    ((hz.mono hWV).sub (hP.mono hWV)) hs0 hpulse.le hcover.1 hcover.2
    (fun x hx => hTW (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx)))
    (fun x hx => averagedQCoefficient_lower hgRefV hV
      (hseg _ (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx))) 5
      (fun sigma hsigma => (hmargin _ (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx)) sigma hsigma).2)) i
  exact hgrad.trans (mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg _))

end SmoothLocal.HighEquation

end

end OAI
