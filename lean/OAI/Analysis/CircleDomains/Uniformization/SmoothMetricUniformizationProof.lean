import OAI.Analysis.CircleDomains.Uniformization.SmoothMetricPlaneModel
import OAI.Analysis.CircleDomains.Topology.PrincipalSphereCharts
import OAI.Analysis.CircleDomains.Topology.ConformalSphericalMetric
import OAI.Analysis.CircleDomains.Uniformization.SmoothMetricUniformization

namespace OAI

/-! Smooth compact metric uniformization for the exact application,
constructed from the existing smooth principal Beltrami solution. -/
open Set Filter Function
open scoped Matrix.Norms.Elementwise Topology ContDiff OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma metric_plane_model_exterior_holomorphic
    {g : (ℝ × ℝ) → PlanarMetric} {F : ℂ ≃ₜ ℂ}
    (hmetric : ∀ z : ℂ, IsMetricConformalAt g F.onePointCongr (z : Sphere))
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R,
      g z = sphericalMetricFactor z • 1) :
    ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z := by
  obtain ⟨R, _, hR⟩ := hfar
  have hc : IsCompact (Complex.equivRealProdCLM ⁻¹' Metric.closedBall 0 R) :=
    Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  rw [Metric.cobounded_eq_cocompact]
  filter_upwards [hc.compl_mem_cocompact] with z hz
  have hg := hR (Complex.equivRealProdCLM z) hz
  have hm := (hmetric z).isConformalAt
    ⟨sphericalMetricFactor (Complex.equivRealProdCLM z), sphericalMetricFactor_pos _, by
      simpa [sphereChartMetric, finiteCoord] using hg⟩
  obtain ⟨_, d, _, hd⟩ := hm
  have hd' : HasDerivAt (F : ℂ → ℂ) d z := by
    change HasDerivAt (sphereLocalMap F.onePointCongr (z : Sphere)) d
      (chart (z : Sphere) (z : Sphere)) at hd
    simpa only [sphereLocalMap_onePointCongr_coe, chart_coe_self] using hd
  exact hd'.differentiableAt

lemma smoothCompactMetricSphereUniformization : SmoothCompactMetricSphereUniformization := by
  intro g hg hPD hfar
  obtain ⟨F, hF, hFi, hlim, hmetric⟩ := smooth_metric_plane_model g hg hPD hfar
  have hhol := metric_plane_model_exterior_holomorphic hmetric hfar
  have hlim' : Tendsto (fun z => F z - z) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using hlim
  obtain ⟨ha, hd⟩ := principalInversionGerm_analytic_deriv hhol hlim'
  have halocal : AnalyticAt ℂ (sphereLocalMap F.onePointCongr ∞) 0 := by
    rwa [sphereLocalMap_onePointCongr_infty]
  have hdlocal : HasDerivAt (sphereLocalMap F.onePointCongr ∞) 1 0 := by
    rwa [sphereLocalMap_onePointCongr_infty]
  have hfix : F.onePointCongr ∞ = (∞ : Sphere) := rfl
  have hai := analyticAt_inverse_sphereLocalMap_infty F.onePointCongr hfix halocal
    (by rw [hdlocal.deriv]; exact one_ne_zero)
  refine ⟨F.onePointCongr, ?_, ?_, ?_⟩
  · intro p
    cases p using OnePoint.rec with
    | infty =>
      have hconf : IsConformalAt F.onePointCongr OnePoint.infty :=
        ⟨F.onePointCongr.continuous.continuousAt, 1, one_ne_zero,
          by
            convert hdlocal using 1 <;> first | rfl | exact chart_infty_self⟩
      exact hconf.isMetricConformalAt_of_scalar (c := 4)
        (by norm_num) (by simp [sphereChartMetric])
    | coe z => exact hmetric z
  · intro p
    cases p using OnePoint.rec with
    | infty => exact ⟨F.onePointCongr.continuous.continuousAt,
        by simpa only [chart_infty_self] using halocal.contDiffAt.restrict_scalars ℝ⟩
    | coe z =>
      refine ⟨F.onePointCongr.continuous.continuousAt, ?_⟩
      rw [sphereLocalMap_onePointCongr_coe, chart_coe_self]
      exact hF.contDiffAt
  · intro p
    cases p using OnePoint.rec with
    | infty => exact ⟨F.onePointCongr.symm.continuous.continuousAt,
        by simpa only [chart_infty_self] using hai.contDiffAt.restrict_scalars ℝ⟩
    | coe z =>
      refine ⟨F.onePointCongr.symm.continuous.continuousAt, ?_⟩
      change ContDiffAt ℝ (↑(⊤ : ENat)) (sphereLocalMap F.symm.onePointCongr (z : Sphere))
        (chart (z : Sphere) (z : Sphere))
      rw [sphereLocalMap_onePointCongr_coe, chart_coe_self]
      exact hFi.contDiffAt

end CircleDomainRigidity

end

end OAI
