import OAI.Geometry.IsometricImmersion.Flows.PatchFlowCoercivity

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem patch_actual_directed_near_coercivity
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
    {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hDarboux : ∀ p ∈ U,
      (covHessian (g0 + eta) z p).det = gaussianCurvature (g0 + eta) p * heightEnergy (g0 + eta) z p)
    (hyy : ∀ p ∈ U, covHessian (g0 + eta) z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy (g0 + eta) z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    (cG rhoMax epsilon MG MI MB Mr MA MAs MG1 c1 D edge lambda : ℝ)
    (hkappa : 0 < kappa) (hcG : 0 < cG) (hG : cG ≤ heightChartG1 (g0 + eta) z Y p)
    (hrhoMax : capChartRho Y p ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hqbudget : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGs : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hGt : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hKsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (hIs : |coordPartial 1 (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤ MI)
    (hBp : |heightChartB (g0 + eta) z Y ell p| ≤ MB)
    (hr : |heightChartRemainder (g0 + eta) z Y ell p| ≤ Mr)
    (hAp : |heightChartA (g0 + eta) z Y p| ≤ MA)
    (hAs : |coordPartial 1 (heightChartA (g0 + eta) z Y) p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda)
    (hEbudget : (MI + 1 + 2 * MB) / 2 + Mr ≤ lambda / 8)
    (hcrossbudget : 4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 *
      epsilon^2 * MA ≤ 1 / 8)
    (hloss : (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 8)
    (hGmax : heightChartG1 (g0 + eta) z Y p ≤ MG1)
    (hc1 : 0 ≤ c1) (hdist : edge - p 1 ≤ D)
    (hKstrip : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ c1 * (edge - p 1))
    (hstripbudget : MG1 * c1 * (lambda * D + 8) ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 6)
    (x y : ℝ) :
    let A := heightChartA (g0 + eta) z Y
    let B := heightChartB (g0 + eta) z Y ell
    let C := heightChartC (g0 + eta) z Y ell
    let I := coordinatePrimitive B
    min (lambda / 8) (modelCoercivityMargin cG kappa rhoMax epsilon ell / 4) *
      directedWeight edge lambda I p * (x^2 + y^2) ≤
      multiplierT B (directedM edge lambda I) (directedN edge lambda epsilon I) p * x^2 +
        multiplierS A C (directedM edge lambda I) (directedN edge lambda epsilon I) p * y^2 +
        multiplierJ A B C (directedM edge lambda I) (directedN edge lambda epsilon I) p * x * y := by
  let mu := modelCoercivityMargin cG kappa rhoMax epsilon ell / 2
  have hmu : 0 < mu := div_pos
    (modelCoercivityMargin_pos ell hcG hkappa ((capChartRho_pos hY hvar hp).trans_le hrhoMax) heps)
    (by norm_num)
  have hA : DifferentiableAt ℝ (heightChartA (g0 + eta) z Y) p :=
    ((heightChartA_contDiffOn hg hU hz hyy hY hvar hmap).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hB : ContDiffOn ℝ ∞ (heightChartB (g0 + eta) z Y ell) (coordinateRectangle 2 (-2) 2) :=
    heightChartB_contDiffOn hg hU hz hyy hY hmap ell
  have hC := heightChartC_factor hg hU hz hDarboux hyy hE hY hvar hmap hp ell
  have hprincipal : mu ≤ directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p :=
    patch_heightChart_near_principal_lower hg hU hz hyy hY hode hvar hdisp hqsmall hmap
      hbackground hsupport hcentral hp hs ell hkappa hcG hG hrhoMax heps heps1 hqbudget hGs hGt hKsmall
  have hstrip : 0 < heightChartA (g0 + eta) z Y p →
      weightH0 edge lambda p * heightChartA (g0 + eta) z Y p ≤ mu / 3 := by
    intro hpositive
    rw [heightChartA_eq]
    apply actual_positive_curvature_strip_budget (sub_pos.mpr hedge) hdist hc1 hlambda.le
      (hcG.trans_le hG).le hGmax hKstrip
    dsimp only [mu]
    linarith
  have hloss' : (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
      mu / 4 := by dsimp only [mu]; linarith
  have hh := primitive_directed_near_coercivity hB (by norm_num : (0 : ℝ) < 2) hp
    (heightChartA (g0 + eta) z Y) (heightChartC (g0 + eta) z Y ell)
    (heightChartRemainder (g0 + eta) z Y ell) hA edge lambda epsilon ell hedge hlambda
    heps.le heps1 hC MI MB Mr MA MAs mu hmu hIs hBp hr hAp hAs hTbudget hEbudget hcrossbudget
    hloss' hprincipal hstrip x y
  have hm : mu / 2 = modelCoercivityMargin cG kappa rhoMax epsilon ell / 4 := by
    dsimp only [mu]
    ring
  rw [hm] at hh
  exact hh

end SmoothLocal.Flow

end

end OAI
