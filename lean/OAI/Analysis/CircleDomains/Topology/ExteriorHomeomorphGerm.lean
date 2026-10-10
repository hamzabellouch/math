import OAI.Analysis.CircleDomains.Topology.HolomorphicHomeomorph
import OAI.Analysis.CircleDomains.Topology.PrincipalSphereCharts
import OAI.Analysis.CircleDomains.Topology.SphereLocalMapInjective

namespace OAI

/-! A plane homeomorphism holomorphic near infinity has an analytic
inversion germ. No principal normalization is required here. -/
open Filter Set
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_homeomorph_inversion_analytic (F : ℂ ≃ₜ ℂ)
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    AnalyticAt ℂ (principalInversionGerm F) 0 := by
  have hc := continuousAt_sphereLocalMap
    (f := (F.onePointCongr : Sphere → Sphere)) (p := OnePoint.infty)
    F.onePointCongr.continuous.continuousAt
  rw [sphereLocalMap_onePointCongr_infty, chart_infty_self] at hc
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  have hn : ∀ᶠ z in Bornology.cobounded ℂ, F z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    filter_upwards [(isCompact_singleton : IsCompact ({F.symm 0} : Set ℂ)).compl_mem_cocompact]
      with z hz
    intro hzero
    apply hz
    exact F.injective (hzero.trans (F.apply_symm_apply 0).symm)
  have hd := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually (hF.and hn)
  filter_upwards [hd, self_mem_nhdsWithin] with w hw hw0
  have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hw0
  have hcomp := (hw.1.comp w hi).inv hw.2
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hw0] with z hz
  exact Function.update_of_ne hz _ _

lemma exterior_homeomorph_conformalAt_infty (F : ℂ ≃ₜ ℂ)
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    IsConformalAt F.onePointCongr OnePoint.infty := by
  have ha : AnalyticAt ℂ (sphereLocalMap F.onePointCongr OnePoint.infty)
      (chart OnePoint.infty OnePoint.infty) := by
    rw [sphereLocalMap_onePointCongr_infty, chart_infty_self]
    exact exterior_homeomorph_inversion_analytic F hF
  refine ⟨F.onePointCongr.continuous.continuousAt, _,
    sphereLocalMap_deriv_ne_zero F.onePointCongr OnePoint.infty ha, ?_⟩
  convert ha.differentiableAt.hasDerivAt using 1
  rfl

lemma exterior_homeomorph_conformalOn (F : ℂ ≃ₜ ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hF : ∀ z ∉ K, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    IsConformalOn F.onePointCongr (((↑) : ℂ → Sphere) '' K)ᶜ := by
  have hdiff : DifferentiableOn ℂ (F : ℂ → ℂ) Kᶜ :=
    fun z hz => (hF z hz).differentiableWithinAt
  intro p hp
  cases p using OnePoint.rec with
  | infty =>
    apply exterior_homeomorph_conformalAt_infty F
    rw [Metric.cobounded_eq_cocompact]
    filter_upwards [hK.compl_mem_cocompact] with z hz
    exact hF z hz
  | coe z =>
    have hz : z ∉ K := by
      intro hz
      exact hp (mem_image_of_mem _ hz)
    refine ⟨F.onePointCongr.continuous.continuousAt, deriv F z,
      holomorphicHomeomorph_deriv_ne_zero F hK.isClosed.isOpen_compl hdiff hz, ?_⟩
    have heq : sphereLocalMap F.onePointCongr (z : Sphere) = F := by
      funext w
      simp [sphereLocalMap, Homeomorph.onePointCongr_apply, chart, chartSymm, finiteCoord]
    change HasDerivAt (sphereLocalMap F.onePointCongr (z : Sphere)) (deriv F z)
      (chart (z : Sphere) (z : Sphere))
    rw [heq, chart_coe_self]
    exact (hF z hz).hasDerivAt

lemma exterior_homeomorph_principal_normalization (F : ℂ ≃ₜ ℂ)
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ (F : ℂ → ℂ) z) :
    ∃ (a b : ℂ) (ha : a ≠ 0),
      IsPrincipalNormalized (affineSphere a b ha ∘ F.onePointCongr) := by
  rw [Metric.cobounded_eq_cocompact] at hF
  obtain ⟨K, hK, hKF⟩ := Filter.mem_cocompact.mp hF
  have hU : IsOpen ((((↑) : ℂ → Sphere) '' K)ᶜ) :=
    (hK.image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hi : OnePoint.infty ∈ ((((↑) : ℂ → Sphere) '' K)ᶜ) := by simp
  exact principal_normalize_at_infty hU (exterior_homeomorph_conformalOn F hK hKF)
    F.onePointCongr.injective.injOn hi rfl

end CircleDomainRigidity

end

end OAI
