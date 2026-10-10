import OAI.Geometry.IsometricImmersion.Caps.AllOrderCapEstimate
import OAI.Geometry.IsometricImmersion.Caps.PhysicalCapTransport
import OAI.Geometry.IsometricImmersion.Estimates.ActualRemainderRegularity

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem cap_closed_image_properties {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    {tl tr sb st : ℝ} (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
    MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
    volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
    capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare := by
  have hc : IsCompact (capChart Y '' closedRectangle tl tr sb st) :=
    (capRectangle_isCompact _ _ _ _).image_of_continuousOn
      ((capChart_contDiffOn hYs).continuousOn.mono hbox)
  refine ⟨hc,hc.measurableSet,hc.measure_lt_top,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  exact capChart_mem_modelOpenSquare (hbox hp) (hdisp p (hbox hp))

theorem exists_C8_one_flow_physical_cap_estimates
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hzB : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1:ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (V : Set Coord) (Y : ℝ → ℝ → ℝ),
      IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (hessianQuotient (g0+eta) z) V ∧
      CoordinateBound (hessianQuotient (g0+eta) z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2:ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, Y s t ∈ Icc (-3:ℝ) 3) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, |Y s t-s| ≤ (1:ℝ)/50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50) ∧
      (∀ tl tr sb st : ℝ, closedRectangle tl tr sb st ⊆ capChartDomain →
        IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
        MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
        volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
        capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare) ∧
      ∀ m : ℕ,
        (∀ p ∈ capChartDomain,
          multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
            (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
              capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
        ∀ L R bottom top b : ℝ,
          -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
          0 < heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b ∧
          (∫ p in capChart Y '' closedRectangle L R bottom top,
            (coordPartial 0 (verticalJet z (m+3)) p)^2+(verticalJet z (m+4) p)^2) ≤
            heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b*
              ((∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (actualHighRemainder (g0+eta) z m p)^2)+
                (∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (verticalJet z (m+3) p)^2)) := by
  obtain ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,hall⟩ :=
    exists_C8_one_flow_all_high_cap_estimates hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor
      hsmall hD hk hbackground hsupport hcentral
  obtain ⟨_,hsource,_,heq,_,_⟩ :=
    exists_global_triangularFlow_chart hq hV hSV hY hconf hstart hode
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hMq (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial 1 (hessianQuotient (g0+eta) z) p| ≤ M := hqB [1] (by norm_num) p hp
  have hJ (p : Coord) (hp : p ∈ capChartDomain) :=
    capChart_jacobian_bounds hq hV hSV hY hconf hstart hode hM hMq hp
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0+eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian (g0+eta) z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hsmall1 (p : Coord) (hp : p ∈ capChartDomain) :
      |hessianQuotient (g0+eta) z (capChart Y p)| ≤ 1 :=
    (hsmall _ (modelOpenSquare_subset (hmapO hp))).trans (by norm_num)
  refine ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,
    (fun tl tr sb st hbox => cap_closed_image_properties hYs hdisp hbox),?_⟩
  intro m
  obtain ⟨_,_,_,_,_,hPDE,hestimate⟩ := hall m
  refine ⟨hPDE,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  have hT : closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : closedRectangle L R bottom top ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hbottom
  have hOT : capOuterLeft L ≤ capOuterRight R := by linarith
  have hOS : capOuterBottom bottom ≤ b := by linarith
  have hu := verticalJet_contDiffOn modelOpenSquare_isOpen hzO (m+3)
  have hf := actualHighRemainder_contDiffOn hgO modelOpenSquare_isOpen hzO
    (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO m
  have hfI : ContinuousOn (actualHighRemainder (g0+eta) z m)
      (capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b) :=
    hf.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmapO (hT hp))
  have hcap := hestimate L R bottom top b hL hR hbottom hLR hbt htop hb
  rw [heightUniformCapEstimateRHS_eq_factors] at hcap
  have hp := cap_gradient_estimate_to_physical_images hYs hvar hode hsource heq hu
    modelOpenSquare_isOpen hmapO hLR hbt hOT hOS hS hT hsmall1 hJ hfI hcap
  refine ⟨heightPhysicalCapConstant_pos G Z d c e0 kappa (m+3) L R bottom top b,?_⟩
  change (∫ p in capChart Y '' closedRectangle L R bottom top,
      coordinateGradientSquare (verticalJet z (m+3)) p) ≤ _
  exact hp

end SmoothLocal.Flow

end

end OAI
