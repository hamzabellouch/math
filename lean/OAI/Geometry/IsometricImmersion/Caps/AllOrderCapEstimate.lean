import OAI.Geometry.IsometricImmersion.Caps.C8ActualCapEstimate
import OAI.Geometry.IsometricImmersion.Caps.CapFlowUniqueness

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem exists_C8_one_flow_all_high_cap_estimates
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
      ∀ m : ℕ,
        let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
        let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
        let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
        let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
        0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
        (∀ p ∈ capChartDomain,
          multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
            (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
              capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
        ∀ L R bottom top b : ℝ,
          -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
          rectangleIntegral L R bottom top
            (fun p => (coordPartial 0 (capPullback Y (verticalJet z (m+3))) p)^2+
              (coordPartial 1 (capPullback Y (verticalJet z (m+3))) p)^2) ≤
            heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
              (capPullback Y (verticalJet z (m+3)))
              (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  have hg4 (i j : Fin 2) : CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G :=
    (coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)).mono (by norm_num) le_rfl
  have hz5 : CoordinateBound z modelSquare 5 Z := coordinateBound_five_of_frechet_eight hz hU hSU hzB
  obtain ⟨V,hV,hSV,hVU,_,hq,hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG hZ hd hc hg4 hz5 hdet hyy
  obtain ⟨Y,hY,_,hstart,hode,_,hdisp50,hrange,_⟩ := exists_cap_flow hq hV hSV hsmall
  have hconf (s : ℝ) (hs : s ∈ Icc (-2:ℝ) 2) (t : ℝ) (ht : t ∈ Icc (-2:ℝ) 2) :
      Y s t ∈ Icc (-3:ℝ) 3 := abs_le.mp ((hrange s hs t ht).1.trans (by norm_num))
  have hYs := cap_flow_joint_contDiffOn hq hV hSV hY hconf hstart hode
  have hchart := capChart_contDiffOn hYs
  have hvar : ∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s :=
    fun s hs t ht => cap_flow_initial_deriv_pos hq hV hSV hY hconf hstart hode hs ht
  have hdisp (p : Coord) (hp : p ∈ capChartDomain) : |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50 :=
    hdisp50 (p 1) ⟨hp.2.1.le,hp.2.2.le⟩ (p 0) ⟨hp.1.1.le,hp.1.2.le⟩
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0+eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian (g0+eta) z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hPDE (m : ℕ) (p : Coord) (hp : p ∈ capChartDomain) :
      multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
        (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
          capPullback Y (actualHighRemainder (g0+eta) z m) p :=
    actual_flow_high_equation hgO modelOpenSquare_isOpen hzO
      (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO hYs hode hvar hmapO m hp
  refine ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,?_⟩
  intro m
  obtain ⟨Ym,heps,heps1,hlambda,hc1,hc2,_,hstartm,hodem,hdispm,_,hestimatem⟩ :=
    exists_uniform_original_data_actual_high_cap_estimate hg hU hSU hz hG hZ hd hc he0 hg4 hz5
      hdet hyy hEfloor hsmall hD hk hbackground hsupport hcentral m
  have heq := capChart_eqOn_of_same_ode hq hV hSV hstart hode hdisp hstartm hodem hdispm
  refine ⟨heps,heps1,hlambda,hc1,hc2,hPDE m,?_⟩
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
  have huint := capPullback_square_rectangle_eq_of_chart_eqOn heq (verticalJet z (m+3)) hOT hOS hT
  have hfint := capPullback_square_rectangle_eq_of_chart_eqOn heq (actualHighRemainder (g0+eta) z m) hOT hOS hT
  have hRHS : heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
      (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) =
      heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
        (capPullback Ym (verticalJet z (m+3))) (capPullback Ym (actualHighRemainder (g0+eta) z m)) := by
    unfold heightUniformCapEstimateRHS
    rw [huint,hfint]
  rw [capPullback_gradient_rectangle_eq_of_chart_eqOn heq (verticalJet z (m+3)) hLR hbt hS,hRHS]
  exact hestimatem L R bottom top b hL hR hbottom hLR hbt htop hb

end SmoothLocal.Flow

end

end OAI
