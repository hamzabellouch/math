import OAI.Geometry.IsometricImmersion.Immersions.HeightCoefficientRegularity
import OAI.Geometry.IsometricImmersion.Coordinates.PatchGeometry

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

variable {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
variable {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}

theorem patch_capCurvature_eventually_model
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (himage : capChart Y p ∈ U)
    (hsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ kappa / 8) :
    capPullback Y (gaussianCurvature (g0 + eta)) =ᶠ[𝓝 p] capModelCurvature kappa Y := by
  have heq := patch_smallCurvature_eventually_model hk hU hbackground hsupport hcentral himage hsmall
  have hc : ContinuousAt (capChart Y) p :=
    (capChart_contDiffOn hY).continuousOn.continuousAt (capChartDomain_isOpen.mem_nhds hp)
  exact heq.comp_tendsto hc.tendsto

theorem patch_heightChartA_eventually_model
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (himage : capChart Y p ∈ U)
    (hsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ kappa / 8) :
    heightChartA (g0 + eta) z Y =ᶠ[𝓝 p]
      (fun q => heightChartG1 (g0 + eta) z Y q * capModelCurvature kappa Y q) := by
  have heq := patch_capCurvature_eventually_model hY hp hk hU hbackground hsupport hcentral himage hsmall
  filter_upwards [heq] with q hq
  rw [heightChartA_eq, hq]

theorem patch_heightChart_near_principal_lower
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian (g0 + eta) z p 1 1 ≠ 0)
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
    {cG rhoMax epsilon MG : ℝ}
    (hkappa : 0 < kappa) (hcG : 0 < cG) (hG : cG ≤ heightChartG1 (g0 + eta) z Y p)
    (hrhoMax : capChartRho Y p ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hsmall : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGs : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hGt : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hKsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell) :
    modelCoercivityMargin cG kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p := by
  have hK8 := hKsmall.trans (min_le_left _ _)
  have hKeq := patch_capCurvature_eventually_model hY hp hkappa hU hbackground hsupport hcentral
    (hmap hp) hK8
  have hAeq := patch_heightChartA_eventually_model (z := z) hY hp hkappa hU hbackground hsupport hcentral
    (hmap hp) hK8
  have hGsm : ContDiffOn ℝ ∞ (heightChartG1 (g0 + eta) z Y) capChartDomain :=
    (capPullback_contDiffOn hY (darbouxG_contDiffOn hg hU hz hyy) hmap).mul
      ((capChartRho_contDiffOn hY hvar).pow 2)
  have hGdiff := (hGsm.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hKmodel : |capModelCurvature kappa Y p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell := by
    rw [← hKeq.self_of_nhds]
    exact hKsmall
  have hmodel := cap_model_full_principal_lower hY hode hvar hdisp hqsmall hp hs ell hGdiff
    hkappa hcG hG hrhoMax heps heps1 hsmall hGs hGt hKmodel
  have hprincipal : directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p =
      directedPrincipal (fun q => heightChartG1 (g0 + eta) z Y q * capModelCurvature kappa Y q)
        ell epsilon p := by
    unfold directedPrincipal
    rw [coordPartial_eq_of_eventuallyEq hAeq 1, coordPartial_eq_of_eventuallyEq hAeq 0]
  rw [hprincipal]
  exact hmodel

theorem actual_positive_curvature_strip_budget
    {G K d D c1 lambda M mu : ℝ}
    (hd : 0 < d) (hD : d ≤ D) (hc1 : 0 ≤ c1) (hlambda : 0 ≤ lambda)
    (hG : 0 ≤ G) (hGM : G ≤ M) (hK : K ≤ c1 * d)
    (hbudget : M * c1 * (lambda * D + 8) ≤ mu / 3) :
    (lambda + 8 / d) * (G * K) ≤ mu / 3 := by
  have hM : 0 ≤ M := hG.trans hGM
  have hH : 0 ≤ lambda + 8 / d := add_nonneg hlambda (div_nonneg (by norm_num) hd.le)
  have hGK : G * K ≤ M * (c1 * d) :=
    (mul_le_mul_of_nonneg_left hK hG).trans
      (mul_le_mul_of_nonneg_right hGM (mul_nonneg hc1 hd.le))
  calc
    _ ≤ (lambda + 8 / d) * (M * (c1 * d)) := mul_le_mul_of_nonneg_left hGK hH
    _ = M * c1 * (lambda * d + 8) := by field_simp [hd.ne']
    _ ≤ M * c1 * (lambda * D + 8) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hD hlambda) le_rfl) (mul_nonneg hM hc1)
    _ ≤ mu / 3 := hbudget

end SmoothLocal.Flow

end

end OAI
