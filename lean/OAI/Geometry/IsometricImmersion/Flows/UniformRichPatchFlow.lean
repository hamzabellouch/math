import OAI.Geometry.IsometricImmersion.Immersions.HeightNumericParameters
import OAI.Geometry.IsometricImmersion.Energy.DirectedParameterChoice
import OAI.Geometry.IsometricImmersion.Energy.PatchDirectedCoercivity

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem exists_patch_uniform_numeric_directed_flow
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => (g0 + eta) p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0 + eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0 + eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0 + eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0 + eta) z p).det = gaussianCurvature (g0 + eta) p * heightEnergy (g0 + eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (ell : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa ell
    let lambda := heightDirectedLambda G Z d c e0 kappa ell
    let c1 := heightDirectedSlope G Z d c e0 kappa ell
    let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      ContDiffOn ℝ ∞ (heightChartA (g0 + eta) z Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartB (g0 + eta) z Y ell) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartC (g0 + eta) z Y ell) capChartDomain ∧
      ContDiffOn ℝ ∞ (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) capChartDomain ∧
      ContDiffOn ℝ ∞ (capPullback Y (gaussianCurvature (g0 + eta))) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartG1 (g0 + eta) z Y) capChartDomain ∧
      (∀ p ∈ capChartDomain,
        heightG1Lower G Z d c e0 ≤ heightChartG1 (g0 + eta) z Y p ∧
        |coordinatePrimitive (heightChartB (g0 + eta) z Y ell) p| ≤ 2*heightBJetBound G Z d c ell ∧
        (∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤
          heightCapCoefficientBound G Z d c e0 ell) ∧
        (∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0 + eta))) p| ≤
          heightCapCurvatureBound G Z d c) ∧
        |heightChartA (g0 + eta) z Y p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
        (∀ i : Fin 2, |coordPartial i (heightChartA (g0 + eta) z Y) p| ≤
          heightCapCoefficientBound G Z d c e0 ell) ∧
        |heightChartB (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
        |heightChartC (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell) ∧
      ∀ edge : ℝ, edge ≤ 0 → ∀ p ∈ capChartDomain, p 1 < edge →
        capPullback Y (gaussianCurvature (g0 + eta)) p ≤ c1 * (edge - p 1) →
        ∀ x y : ℝ,
          let A := heightChartA (g0 + eta) z Y
          let B := heightChartB (g0 + eta) z Y ell
          let C := heightChartC (g0 + eta) z Y ell
          let I := coordinatePrimitive B
          c2 * directedWeight edge lambda I p * (x^2 + y^2) ≤
            multiplierT B (directedM edge lambda I) (directedN edge lambda epsilon I) p * x^2 +
            multiplierS A C (directedM edge lambda I) (directedN edge lambda epsilon I) p * y^2 +
            multiplierJ A B C (directedM edge lambda I) (directedN edge lambda epsilon I) p * x * y := by
  let M := heightQuotientJetBound G Z d c
  let cG := heightG1Lower G Z d c e0
  let rhoMax := 1 / Real.exp (-2 * M)
  let MG := heightG1JetBound G Z d c
  let MB := heightBJetBound G Z d c ell
  let Mr := heightRemainderBound G Z d c e0 ell
  let MA := heightAJetBound G Z d c
  have hcG : 0 < cG := heightG1Lower_pos hG hZ hd he0
  have hrhoMax : 0 < rhoMax := by dsimp [rhoMax]; positivity
  have hMG : 0 ≤ MG := heightG1JetBound_nonneg hG hZ hd hc
  have hMB : 0 ≤ MB := heightBJetBound_nonneg hG hZ hd hc ell
  have hMr : 0 ≤ Mr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hMA : 0 ≤ MA := heightAJetBound_nonneg hG hZ hd hc
  let epsilon := heightDirectedEpsilon G Z d c e0 kappa ell
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  obtain ⟨heps, heps1, hlambda, hc1, hqbudget, hTbudget, hEbudget,
      hcross, hloss, hfarbudget, hnearstrip, hstripbudget⟩ :=
    heightDirectedNumbers_spec ⟨hG,hZ,hd,hc,he0,hk⟩ ell
  let margin := modelCoercivityMargin cG kappa rhoMax epsilon ell
  let delta := modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell
  let c2 := min (lambda / 8) (margin / 4)
  have hmargin : 0 < margin := modelCoercivityMargin_pos ell hcG hk hrhoMax heps
  have hdelta : 0 < delta := modelPrincipalRadius_pos ell hcG hk hrhoMax heps (by norm_num) hMG
  have hc2 : 0 < c2 := by dsimp [c2]; positivity
  obtain ⟨Y, hchart, hYclosed, hYs, hvar, hstart, hode, hconf, hdisp50, hdisp,
      hrho, hG1s, hG1B, hGfloor, hall⟩ :=
    exists_height_flow_uniform_coefficients hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor hsmall hD
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hmapS : MapsTo (capChart Y) capChartDomain modelSquare :=
    fun p hp => modelOpenSquare_subset (hmapO hp)
  have hAB := heightChartA_bound_one hg hU hSU hG hZ hd hc hgB hdet hYs hvar hode hmapS hsmall
    (fun p hp => (hrho p hp).2.1) hG1s hG1B
  obtain ⟨hBs, hBB, hrs, hrB⟩ := hall ell
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0 + eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hyyn := LowQuotient.denominator_ne_zero hc hyy
  have hyyO := fun p (hp : p ∈ modelOpenSquare) => hyyn p (modelOpenSquare_subset hp)
  have hEO := fun p (hp : p ∈ modelOpenSquare) => he0.trans_le (hEfloor p (modelOpenSquare_subset hp))
  have hDO := fun p (hp : p ∈ modelOpenSquare) => hD p (modelOpenSquare_subset hp)
  have hbackgroundO := fun p (hp : p ∈ modelOpenSquare) => hbackground p (hOU hp)
  have hAs := heightChartA_contDiffOn hgO modelOpenSquare_isOpen hzO hyyO hYs hvar hmapO
  have hKB := heightCurvaturePullback_bound_one hg hU hSU hG hZ hd hc hgB hdet
    hYs hvar hode hmapS hsmall (fun p hp => (hrho p hp).2.1)
  obtain ⟨hMF,hMFA,hMFI,hMFB,hMFC⟩ := heightCapCoefficientBound_dominates hG hZ hd hc he0 ell
  have hfixed (p : Coord) (hp : p ∈ capChartDomain) :
      heightG1Lower G Z d c e0 ≤ heightChartG1 (g0 + eta) z Y p ∧
      |coordinatePrimitive (heightChartB (g0 + eta) z Y ell) p| ≤ 2*heightBJetBound G Z d c ell ∧
      (∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤
        heightCapCoefficientBound G Z d c e0 ell) ∧
      (∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0 + eta))) p| ≤
        heightCapCurvatureBound G Z d c) ∧
      |heightChartA (g0 + eta) z Y p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
      (∀ i : Fin 2, |coordPartial i (heightChartA (g0 + eta) z Y) p| ≤
        heightCapCoefficientBound G Z d c e0 ell) ∧
      |heightChartB (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
      |heightChartC (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell := by
    obtain ⟨hIv,hIi⟩ := heightChartB_primitive_first_bounds ell hMB hBs hBB hp
    exact ⟨hGfloor p hp,hIv,fun i => (hIi i).trans hMFI,
      fun i => hKB [i] (by norm_num) p hp,
      (hAB [] (by norm_num) p hp).trans hMFA,
      fun i => (hAB [i] (by norm_num) p hp).trans hMFA,
      (hBB [] (by norm_num) p hp).trans hMFB,
      (heightChartC_value_bound hG hZ hd hc he0 ell hAB hrB hp).trans hMFC⟩
  refine ⟨Y, heps, heps1, hlambda, hc1, hc2, hchart, hYs, hvar, hstart, hode, hdisp,
    hAs, hBs, heightChartC_contDiffOn hgO modelOpenSquare_isOpen hzO hDO hyyO hEO hYs hvar hmapO ell,
    coordinatePrimitive_contDiffOn hBs,
    capPullback_contDiffOn hYs (gaussianCurvature_contDiffOn hg hU) (fun p hp => hSU (hmapS hp)),
    hG1s,hfixed, ?_⟩
  intro edge hedge0 p hp hedge hKstrip x y
  have hs : p 1 ≤ 0 := (le_of_lt hedge).trans hedge0
  have hdist : edge - p 1 ≤ 2 := by linarith [hp.2.1]
  have hI := (heightChartB_primitive_bounds ell hBs hBB hp).2
  have hBpoint : |heightChartB (g0 + eta) z Y ell p| ≤ MB := hBB [] (by norm_num) p hp
  have hrpoint : |heightChartRemainder (g0 + eta) z Y ell p| ≤ Mr := (hrB p hp).1
  have hApoint : |heightChartA (g0 + eta) z Y p| ≤ MA := hAB [] (by norm_num) p hp
  have hAspoint : |coordPartial 1 (heightChartA (g0 + eta) z Y) p| ≤ MA := hAB [1] (by norm_num) p hp
  have hAtpoint : |coordPartial 0 (heightChartA (g0 + eta) z Y) p| ≤ MA := hAB [0] (by norm_num) p hp
  have hGspoint : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG := hG1B [1] (by norm_num) p hp
  have hGtpoint : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG := hG1B [0] (by norm_num) p hp
  have hGmax : heightChartG1 (g0 + eta) z Y p ≤ MG := (le_abs_self _).trans (hG1B [] (by norm_num) p hp)
  by_cases hnear : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ delta
  · exact patch_actual_directed_near_coercivity hgO modelOpenSquare_isOpen hzO hDO hyyO hEO
      hYs hode hvar hdisp50 hsmall hmapO hbackgroundO hsupport hcentral hp hs ell
      cG rhoMax epsilon MG (2 * MB) MB Mr MA MA MG c1 2 edge lambda hk hcG (hGfloor p hp)
      (hrho p hp).2.2 heps heps1 hqbudget hGspoint hGtpoint hnear hedge hlambda hI hBpoint hrpoint
      hApoint hAspoint hTbudget hEbudget hcross hloss hGmax hc1.le hdist hKstrip hstripbudget x y
  · have hKupper : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ delta :=
      hKstrip.trans ((mul_le_mul_of_nonneg_left hdist hc1.le).trans hnearstrip)
    have hKnegative : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ -delta := by
      by_contra hneg
      exact hnear (abs_le.mpr ⟨(lt_of_not_ge hneg).le, hKupper⟩)
    have hAfar := heightChartA_negative_of_curvature (g0 + eta) z Y p hcG hdelta (hGfloor p hp) hKnegative
    have hloss' :
        (4 * (2 * ((ell : ℝ) * MA + MA * Mr + MA * (2 * MB) + 1))^2 * epsilon^2) / lambda ≤
          (margin / 2) / 4 := by
      calc
        _ ≤ margin / 8 := hloss
        _ = _ := by ring
    have hh := primitive_directed_farnegative_coercivity hBs (by norm_num : (0 : ℝ) < 2) hp
      (heightChartA (g0 + eta) z Y) (heightChartC (g0 + eta) z Y ell)
      (heightChartRemainder (g0 + eta) z Y ell)
      ((hAs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
      edge lambda epsilon ell hedge hlambda heps.le heps1 (hrB p hp).2
      (2 * MB) MB Mr MA MA MA (margin / 2) (cG * delta) (by positivity)
      hI hBpoint hrpoint hApoint hAspoint hTbudget hEbudget hcross hloss' hAtpoint
      (mul_pos hcG hdelta) hAfar hfarbudget x y
    have hhalf : (margin / 2) / 2 = margin / 4 := by ring
    rw [hhalf] at hh
    exact hh

end SmoothLocal.Flow

end

end OAI
