import OAI.Geometry.IsometricImmersion.Flows.UniformRichPatchFlow
import OAI.Geometry.IsometricImmersion.Flows.ActualFlowHighEquation
import OAI.Geometry.IsometricImmersion.Caps.CapInteriorEnergy

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

def heightUniformCapEstimateRHS (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) (u f : Coord → ℝ) : ℝ :=
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
  let M := heightCapCoefficientBound G Z d c e0 ell
  let MK := heightCapCurvatureBound G Z d c
  let glow := heightG1Lower G Z d c e0
  let MI := 2*heightBJetBound G Z d c ell
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  (2/(c2*capInteriorWeightFloor top b lambda MI))*
    ((((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)) +
    ((COverlap*(D^6+HElliptic))*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2)))

theorem exists_uniform_original_data_actual_high_cap_estimate
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1 : ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) (m : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
    let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
    let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
    let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) ∧
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
            (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
  let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
  let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
  let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
  obtain ⟨Y,heps,heps1,hlambda,hc1,hc2,hchart,hYs,hvar,hstart,hode,hdisp,
      hAs,hBs,hCs,hIs,hKs,hG1s,hfixed,hcoercive⟩ :=
    exists_patch_uniform_numeric_directed_flow hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor
      hsmall hD hk hbackground hsupport hcentral (m+3)
  let g := g0+eta
  let u := capPullback Y (verticalJet z (m+3))
  let f := capPullback Y (actualHighRemainder g z m)
  let G1 := heightChartG1 g z Y
  let K := capPullback Y (gaussianCurvature g)
  let A := heightChartA g z Y
  let B := heightChartB g z Y (m+3)
  let C := heightChartC g z Y (m+3)
  let I := coordinatePrimitive B
  let M := heightCapCoefficientBound G Z d c e0 (m+3)
  let MK := heightCapCurvatureBound G Z d c
  let MI := 2*heightBJetBound G Z d c (m+3)
  let glow := heightG1Lower G Z d c e0
  have hM : 0 ≤ M := (heightCapCoefficientBound_dominates hG hZ hd hc he0 (m+3)).1
  have hMK : 0 ≤ MK := heightCapCurvatureBound_nonneg hG hZ hd hc
  have hglow : 0 < glow := heightG1Lower_pos hG hZ hd he0
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hu : ContDiffOn ℝ ∞ u capChartDomain := capPullback_contDiffOn hYs
    (verticalJet_contDiffOn modelOpenSquare_isOpen hzO (m+3)) hmapO
  have hPDE (p : Coord) (hp : p ∈ capChartDomain) : multiplierOperator A B C u p = f p :=
    actual_flow_high_equation hgO modelOpenSquare_isOpen hzO
      (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO hYs hode hvar hmapO m hp
  have hAeq : A = (fun q => G1 q*K q) := by
    funext q
    exact heightChartA_eq g z Y q
  have hPDERaw : ∀ p ∈ capChartDomain, multiplierOperator (fun q => G1 q*K q) B C u p = f p := by
    intro p hp
    rw [←hAeq]
    exact hPDE p hp
  refine ⟨Y,heps,heps1,hlambda,hc1,hc2,hchart,hstart,hode,hdisp,hPDE,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  let T := closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
  let S := closedRectangle L R bottom top
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  let RHS := (((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)) +
    ((COverlap*(D^6+HElliptic))*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2))
  have hT : T ⊆ capChartDomain := capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : S ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  have hcoerceClosed (p : Coord) (hp : p ∈ T) (hK : K p ≤ c1*edgeDistance b p) :
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*K q) B C (directedM b lambda I) (directedN b lambda epsilon I) u p := by
    rw [←hAeq]
    by_cases hedge : p 1 < b
    · have hh := hcoercive b hb p (hT hp) hedge hK (coordPartial 0 u p) (coordPartial 1 u p)
      unfold multiplierQuadratic
      convert hh using 1
    · have heq : p 1 = b := le_antisymm hp.2.2 (le_of_not_gt hedge)
      rw [directedWeight_edge_zero b lambda I p heq,
        directedQuadratic_edge_zero A B C I u b lambda epsilon p
          ((hAs.contDiffAt (capChartDomain_isOpen.mem_nhds (hT hp))).differentiableAt (by simp))
          ((hIs.contDiffAt (capChartDomain_isOpen.mem_nhds (hT hp))).differentiableAt (by simp)) heq]
      simp
  have hlow (p : Coord) (hp : p ∈ T) := hfixed p (hT hp)
  have hAvRaw (p : Coord) (hp : p ∈ T) : |G1 p*K p| ≤ M := by
    rw [←heightChartA_eq g z Y p]
    exact (hlow p hp).2.2.2.2.1
  have hAiRaw (p : Coord) (hp : p ∈ T) (i : Fin 2) : |coordPartial i (fun q => G1 q*K q) p| ≤ M := by
    rw [←hAeq]
    exact (hlow p hp).2.2.2.2.2.1 i
  have hi : (c2/2)*rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
      (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ RHS :=
    actual_cap_integrated_overlap_estimate hL hR hbottom (hbt.trans htop.le) hb hk hc1 hc2 hglow hM hMK
      hlambda.le heps.le heps1 hKs hG1s hBs hCs hIs hu hPDERaw hbackground hsupport
      (fun p hp => hOU (hmapO (hT hp))) (fun p hp => hdisp p (hT hp))
      (fun p hp => (hlow p hp).2.1) (fun p hp => (hlow p hp).2.2.1)
      (fun p hp => (hlow p hp).1) hAvRaw hAiRaw
      (fun p hp => (hlow p hp).2.2.2.2.2.2.1) (fun p hp => (hlow p hp).2.2.2.2.2.2.2)
      (fun p hp => (hlow p hp).2.2.2.1) hcoerceClosed
  have hinterior := capInterior_gradient_le_directed_energy hL hR hbottom hLR hbt htop hb
    hlambda.le hIs hu (fun p hp => (hfixed p (hS hp)).2.1)
  have hWpos : 0 < capInteriorWeightFloor top b lambda MI := capInteriorWeightFloor_pos htop
  have hden : 0 < c2/2 := by positivity
  have henergy : rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
      (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ (2/c2)*RHS := by
    have hh : rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
        (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ RHS/(c2/2) :=
      (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hi)
    have hscale (value : ℝ) : value/(c2/2) = (2/c2)*value := by
      rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm]
    rw [hscale RHS] at hh
    exact hh
  have hfinal := hinterior.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  change rectangleIntegral L R bottom top (fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤ _
  have hscale : (1/capInteriorWeightFloor top b lambda MI)*(2/c2) =
      2/(c2*capInteriorWeightFloor top b lambda MI) := by
    rw [div_mul_div_comm, one_mul, mul_comm (capInteriorWeightFloor top b lambda MI)]
  calc
    _ ≤ (1/capInteriorWeightFloor top b lambda MI)*((2/c2)*RHS) := hfinal
    _ = (2/(c2*capInteriorWeightFloor top b lambda MI))*RHS := by rw [←mul_assoc,hscale]
    _ = _ := rfl

end SmoothLocal.Flow

end

end OAI
