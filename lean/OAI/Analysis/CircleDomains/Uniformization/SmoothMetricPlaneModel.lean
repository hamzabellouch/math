import OAI.Analysis.CircleDomains.Uniformization.SmoothMetricCoefficient
import OAI.Analysis.CircleDomains.Uniformization.MetricConformality
import OAI.Geometry.Cannon.Beltrami.TwoPointNormalize

namespace OAI

/-! A principally normalized smooth plane model for the actual metric.
The finite-point metric equations are derived from the constructed coefficient. -/
open Set Filter
open scoped Matrix.Norms.Elementwise Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma sphereLocalMap_onePointCongr_coe (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    sphereLocalMap F.onePointCongr (z : Sphere) = F := by
  funext w
  simp [sphereLocalMap, Homeomorph.onePointCongr_apply, chart, chartSymm, finiteCoord]

lemma smooth_metric_plane_model
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R,
      g z = sphericalMetricFactor z • 1) :
    ∃ F : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (F : ℂ → ℂ) ∧
      ContDiff ℝ ∞ (F.symm : ℂ → ℂ) ∧
      Tendsto (fun z => F z - z) (Filter.cocompact ℂ) (𝓝 0) ∧
      ∀ z : ℂ, IsMetricConformalAt g F.onePointCongr (z : Sphere) := by
  obtain ⟨μ, hμc, hμ, k, hk, hbound⟩ := exists_smooth_metric_coefficient g hg hPD (by
    obtain ⟨R, hR, hout⟩ := hfar
    exact ⟨R, hR, fun z hz => ⟨sphericalMetricFactor z, hout z hz⟩⟩)
  obtain ⟨F, hF, hlim, he, hn⟩ := CannonBeltrami.smooth_beltrami_homeomorph μ hμc
    k.coe_nonneg (by exact_mod_cast hk) hbound
  have hFi := CannonBeltrami.contDiff_symm_beltrami F hF μ
    (fun z => (hbound z).trans_lt (by exact_mod_cast hk)) he hn
  refine ⟨F, hF, hFi, hlim, ?_⟩
  intro z
  have hL (w : ℂ) : fderiv ℝ (F : ℂ → ℂ) z w =
      CannonBeltrami.partialZ F z * w +
        (metricBeltramiCoefficient (g (Complex.equivRealProdCLM z)) *
          CannonBeltrami.partialZ F z) * star w := by
    rw [CannonBeltrami.fderiv_wirtinger, he, hμ]
  obtain ⟨s, hs, hxx, hyy, hxy, hdet⟩ := metric_gram_of_beltrami_linear
    (hPD (Complex.equivRealProdCLM z)) (fderiv ℝ (F : ℂ → ℂ) z)
    (CannonBeltrami.partialZ F z) (hn z) hL
  have hchart : chart (z : Sphere) (z : Sphere) = z := by
    simp [chart, finiteCoord]
  have hmetric : sphereChartMetric g (z : Sphere) = g (Complex.equivRealProdCLM z) := by
    simp [sphereChartMetric, finiteCoord]
  refine ⟨F.onePointCongr.continuous.continuousAt, ?_, ?_⟩
  · rw [sphereLocalMap_onePointCongr_coe]
    exact hF.differentiable (by simp) _
  · simpa only [sphereLocalMap_onePointCongr_coe, hchart, hmetric] using
      (show ∃ s : ℝ, 0 < s ∧
        (fderiv ℝ (F : ℂ → ℂ) z 1).re^2 + (fderiv ℝ (F : ℂ → ℂ) z 1).im^2 =
          s * g (Complex.equivRealProdCLM z) 0 0 ∧
        (fderiv ℝ (F : ℂ → ℂ) z Complex.I).re^2 +
          (fderiv ℝ (F : ℂ → ℂ) z Complex.I).im^2 = s * g (Complex.equivRealProdCLM z) 1 1 ∧
        (fderiv ℝ (F : ℂ → ℂ) z 1).re * (fderiv ℝ (F : ℂ → ℂ) z Complex.I).re +
          (fderiv ℝ (F : ℂ → ℂ) z 1).im * (fderiv ℝ (F : ℂ → ℂ) z Complex.I).im =
            s * g (Complex.equivRealProdCLM z) 0 1 ∧
        0 < (fderiv ℝ (F : ℂ → ℂ) z 1).re * (fderiv ℝ (F : ℂ → ℂ) z Complex.I).im -
          (fderiv ℝ (F : ℂ → ℂ) z Complex.I).re * (fderiv ℝ (F : ℂ → ℂ) z 1).im from
        ⟨s, hs, hxx, hyy, hxy, hdet⟩)

end CircleDomainRigidity

end

end OAI
