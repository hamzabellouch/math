import OAI.Geometry.IsometricImmersion.Caps.CapCutoffRectangle

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capDistanceBound (A b : ℝ) : ℝ := b-capOuterBottom A

def capOverlapEnergyCost (L R A b kappa c1 c2 glow M lambda MI : ℝ) : ℝ :=
  let D := capDistanceBound A b
  let c := capOverlapThreshold kappa c1 D
  (directedFluxCostConstant D M lambda 2 MI (capSpatialDerivativeConstant L R A) +
    directedDefectCostConstant D M lambda 2 MI c2)*(D+1/(glow*c))

def capEllipticRatioBudget (L R A b kappa c1 glow MK M : ℝ) : ℝ :=
  let D := capDistanceBound A b
  let c := capOverlapThreshold kappa c1 D
  ellipticRatioConstant D (glow*c/2)
    (ellipticCutoffDerivativeConstant c MK
      (threeEdgeDerivativeConstant (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
        (capOuterRight R) (capOuterBottom A) (capOuterBottomOne A))) M

theorem directedForcingEnergy_bound
    {chi I f : Coord → ℝ} {p : Coord} {b lambda D S MI : ℝ}
    (hlambda : 0 ≤ lambda) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    directedForcingEnergy chi I f b lambda p ≤ D^8*Real.exp (lambda*S+MI)*(f p)^2 := by
  have hD : 0 ≤ D := hd.trans hdD
  have hW0 : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hW7 := directedWeight_le_seven hlambda hd hdD hs hI
  have hdpow := pow_le_pow_left₀ hd hdD 7
  have hW : directedWeight b lambda I p ≤ D^8*Real.exp (lambda*S+MI) := by
    calc
      _ ≤ D*Real.exp (lambda*S+MI)*edgeDistance b p^7 := hW7
      _ ≤ D*Real.exp (lambda*S+MI)*D^7 :=
        mul_le_mul_of_nonneg_left hdpow (by positivity)
      _ = _ := by ring
  have hchiW := mul_le_mul hchi.2 hW hW0 (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul, directedForcingEnergy] using mul_le_mul_of_nonneg_right hchiW (sq_nonneg (f p))

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem actual_cap_integrated_overlap_estimate
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A0 b kappa c1 c2 glow lambda epsilon MI M MK : ℝ}
    {G1 B C I u f : Coord → ℝ}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0) (hAb : A0 ≤ b) (hb : b ≤ 0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hc2 : 0 < c2) (hg : 0 < glow)
    (hM : 0 ≤ M) (hMK : 0 ≤ MK) (hlambda : 0 ≤ lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hK : ContDiffOn ℝ ∞ (capPullback Y (gaussianCurvature (g0+eta))) capChartDomain)
    (hG1 : ContDiffOn ℝ ∞ G1 capChartDomain) (hB : ContDiffOn ℝ ∞ B capChartDomain)
    (hC : ContDiffOn ℝ ∞ C capChartDomain) (hI : ContDiffOn ℝ ∞ I capChartDomain)
    (hu : ContDiffOn ℝ ∞ u capChartDomain)
    (hEq : ∀ p ∈ capChartDomain,
      multiplierOperator (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C u p = f p)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox)
    (himage : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capChart Y p ∈ U)
    (hdisp : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hIv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |I p| ≤ MI)
    (hIi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hGlow : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, glow ≤ G1 p)
    (hAv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |G1 p*capPullback Y (gaussianCurvature (g0+eta)) p| ≤ M)
    (hAi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p| ≤ M)
    (hBv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |B p| ≤ M)
    (hCv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |C p| ≤ M)
    (hKi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0+eta))) p| ≤ MK)
    (hcoercive : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capPullback Y (gaussianCurvature (g0+eta)) p ≤ c1*edgeDistance b p →
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C
          (directedM b lambda I) (directedN b lambda epsilon I) u p) :
    let D := capDistanceBound A0 b
    let COverlap := capOverlapEnergyCost L R A0 b kappa c1 c2 glow M lambda MI
    let HElliptic := capEllipticRatioBudget L R A0 b kappa c1 glow MK M
    (c2/2)*rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b
      (directedGradientEnergy (capSpatialCutoff L R A0) I u b lambda) ≤
      ((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (f p)^2) +
      (COverlap*(D^6+HElliptic))*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (u p)^2) := by
  let tl := capOuterLeft L
  let tr := capOuterRight R
  let sb := capOuterBottom A0
  let D := capDistanceBound A0 b
  let c := capOverlapThreshold kappa c1 D
  let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
  let K := capPullback Y (gaussianCurvature (g0+eta))
  let chi := capSpatialCutoff L R A0
  let chi2 := capOuterSpatialCutoff L R A0
  let v := ellipticWeightC1 b c chi2 K
  let E := ellipticEnergy A v u
  let Err := directedCutoffError A chi I u b lambda epsilon
  let Def := directedCoercivityDefect A B C chi I u b lambda epsilon c2
  let COverlap := capOverlapEnergyCost L R A0 b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R A0 b kappa c1 glow MK M
  obtain ⟨htlo,htwidth,htone,hrone,hrwidth,htrhi,hsblo,hswidth,hsone,hlt,hrt⟩ :=
    capOuterRectangle_edges hL hR hA0
  have ht : tl ≤ tr := by dsimp only [tl,tr]; linarith
  have hs : sb ≤ b := by dsimp only [sb]; linarith
  have hD : 0 ≤ D := sub_nonneg.mpr hs
  have hc : 0 < c := capOverlapThreshold_pos hk hc1 hD
  have hbox : closedRectangle tl tr sb b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hA0 (by linarith)
  have hA : ContDiffOn ℝ ∞ A capChartDomain := hG1.mul hK
  have hchi : ContDiffOn ℝ ∞ chi capChartDomain := (capSpatialCutoff_contDiff _ _ _).contDiffOn
  have hchi2 : ContDiffOn ℝ ∞ chi2 capChartDomain := (capOuterSpatialCutoff_contDiff _ _ _).contDiffOn
  have hv : ContDiffOn ℝ 1 v capChartDomain := ellipticWeightC1_contDiffOn hc
    (hchi2.of_le (by simp)) (hK.of_le (by simp))
  have hW := directedWeight_contDiffOn b lambda hI
  have hm := hW.neg
  have hn : ContDiffOn ℝ ∞ (directedN b lambda epsilon I) capChartDomain :=
    (contDiffOn_const.mul (contDiffOn_apply ℝ ℝ 0 _)).mul hW
  have hut := partial_contDiffOn hu capChartDomain_isOpen 0
  have hus := partial_contDiffOn hu capChartDomain_isOpen 1
  have hgrad := (hut.pow 2).add (hus.pow 2)
  have hQ := multiplierQuadratic_contDiffOn capChartDomain_isOpen hA hB hC hm hn hu
  have hErr : ContinuousOn Err (closedRectangle tl tr sb b) :=
    (multiplierCutoffError_contDiffOn capChartDomain_isOpen hA hchi hm hn hu).continuousOn.mono hbox
  have hDef : ContinuousOn Def (closedRectangle tl tr sb b) :=
    (hchi.continuousOn.mul ((continuousOn_const (c := (0 : ℝ))).sup
      ((((contDiffOn_const (c := c2)).mul hW).mul hgrad).sub hQ).continuousOn)).mono hbox
  obtain ⟨_,_,hEnergy,_⟩ := elliptic_fields_C1 capChartDomain_isOpen hA hB hC hv hu
  have hE : ContinuousOn E (closedRectangle tl tr sb b) := hEnergy.mono hbox
  have hX : 0 ≤ capSpatialDerivativeConstant L R A0 :=
    (abs_nonneg _).trans (capSpatialCutoff_partial_uniform hL hR hA0 (boxPoint 0 0) 0)
  have hconst := directedCostConstants_nonneg (S := 2) (MI := MI) hD hM hlambda hX hc2.le
  have hOverlap : 0 ≤ COverlap := by
    dsimp only [COverlap,capOverlapEnergyCost]
    exact mul_nonneg (add_nonneg hconst.1 hconst.2) (by positivity)
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb b) : |Err p|+Def p ≤ COverlap*E p := by
    have hpD := hbox hp
    exact actual_cap_directed_costs_le_elliptic hL hR hA0 hk hc1 hc2.le hg hD hM hlambda heps heps1
      hbackground hsupport (himage p hp) (hdisp p hp) hp.2.2
      (by dsimp only [edgeDistance,D,capDistanceBound]; linarith [hp.2.1])
      (abs_lt.mpr hpD.1).le (abs_lt.mpr hpD.2).le (hIv p hp)
      ((hI.contDiffAt (capChartDomain_isOpen.mem_nhds hpD)).differentiableAt (by simp)) (hIi p hp)
      (hGlow p hp) ((hA.contDiffAt (capChartDomain_isOpen.mem_nhds hpD)).differentiableAt (by simp))
      (hAv p hp) (hAi p hp) (hBv p hp) (hCv p hp) (hcoercive p hp)
  have hcostIntegral := rectangleIntegral_mono ht hs (hErr.abs.add hDef) (continuousOn_const.mul hE) hpoint
  change rectangleIntegral tl tr sb b (fun p => |Err p| + Def p) ≤
    rectangleIntegral tl tr sb b (fun p => COverlap * E p) at hcostIntegral
  rw [rectangleIntegral_add ht hs hErr.abs hDef, rectangleIntegral_const_mul] at hcostIntegral
  have hEllRaw := threeEdge_elliptic_energy_bound htwidth hrwidth hswidth ht hs hc hMK hg hM
    capChartDomain_isOpen hK hG1 hB hC hu hbox hEq hKi hGlow hAv (fun p hp => hAi p hp 1) hBv hCv
  have hEll : rectangleIntegral tl tr sb b E ≤
      D^6*rectangleIntegral tl tr sb b (fun p => (f p)^2) +
        (D^6+HElliptic)*rectangleIntegral tl tr sb b (fun p => (u p)^2) := by
    calc
      _ = rectangleIntegral tl tr sb b
          (ellipticEnergy A (ellipticWeight b c
            (threeEdgeCutoff (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
              (capOuterRight R) (capOuterBottom A0) (capOuterBottomOne A0)) K) u) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        change ellipticWeightC1 b c chi2 K p * _ = _
        rw [ellipticWeightC1_eq hp.2.2]
        change ellipticWeight b c (capOuterSpatialCutoff L R A0) K p * _ = _
        rw [capOuterSpatialCutoff_eq_threeEdge]
        rfl
      _ ≤ _ := hEllRaw
  have hf : ContDiffOn ℝ ∞ f capChartDomain :=
    (ellipticOperator_contDiffOn capChartDomain_isOpen hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  have hF : ContinuousOn (directedForcingEnergy chi I f b lambda) (closedRectangle tl tr sb b) :=
    (((hchi.mul hW).mul (hf.pow 2)).continuousOn.mono hbox)
  have hf2 : ContinuousOn (fun p => (f p)^2) (closedRectangle tl tr sb b) := (hf.pow 2).continuousOn.mono hbox
  have hforcing := rectangleIntegral_mono ht hs hF (continuousOn_const.mul hf2)
    (fun p hp => directedForcingEnergy_bound hlambda (sub_nonneg.mpr hp.2.2)
      (show edgeDistance b p ≤ D by dsimp only [edgeDistance,D,capDistanceBound]; linarith [hp.2.1])
      (abs_lt.mpr (hbox hp).2).le (hIv p hp) (capSpatialCutoff_range L R A0 p))
  change rectangleIntegral tl tr sb b (directedForcingEnergy chi I f b lambda) ≤
    rectangleIntegral tl tr sb b (fun p => (D^8*Real.exp (lambda*2+MI)) * (f p)^2) at hforcing
  rw [rectangleIntegral_const_mul] at hforcing
  obtain ⟨hsides,hbottom⟩ := capSpatialCutoff_outer_boundary (b := b) hL hR hA0
  have hdir := integrated_directed_energy_with_explicit_costs ht hs capChartDomain_isOpen hA hB hC
    hchi hI hu hbox hsides hbottom hEq (fun p _ => (capSpatialCutoff_range L R A0 p).1)
      lambda epsilon 2 c2 hc2 heps heps1 (fun p hp => (abs_lt.mpr (hbox hp).1).le)
  norm_num only [show (1 : ℝ)+2^2=5 by norm_num] at hdir
  have hsourceConstant : 0 ≤ (5 : ℝ)/(2*c2) := by positivity
  have hcombined := add_le_add (mul_le_mul_of_nonneg_left hforcing hsourceConstant)
    (hcostIntegral.trans (mul_le_mul_of_nonneg_left hEll hOverlap))
  change (c2/2)*rectangleIntegral tl tr sb b (directedGradientEnergy chi I u b lambda) ≤ _
  exact hdir.trans (by
    convert hcombined using 1 <;> (first | rfl | ring))

end SmoothLocal.Flow

end

end OAI
