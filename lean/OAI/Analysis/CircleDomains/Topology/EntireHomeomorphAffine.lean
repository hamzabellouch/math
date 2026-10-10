import OAI.Analysis.CircleDomains.Topology.ExteriorHomeomorphGerm

namespace OAI

/-! An entire plane homeomorphism is affine. Its analytic infinity germ
supplies principal normalization, after which Liouville applies to the
entire remainder. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma entire_homeomorph_affine (F : ℂ ≃ₜ ℂ) (hF : Differentiable ℂ (F : ℂ → ℂ)) :
    ∃a b : ℂ,a≠0 ∧ ∀z,F z=a*z+b := by
  obtain ⟨a,b,ha,hp⟩ := exterior_homeomorph_principal_normalization F (.of_forall hF)
  have ht := principal_remainder_tendsto_zero hp.2
  have he : Tendsto (fun z => a*F z+b-z) (cocompact ℂ) (𝓝 0) := by
    rw [←Metric.cobounded_eq_cocompact]
    simpa only [comp_apply,Homeomorph.onePointCongr_apply,OnePoint.map_some,affineSphere_coe,finiteCoord_coe] using ht
  have hd : Differentiable ℂ (fun z => a*F z+b-z) := by fun_prop
  have hz (z : ℂ) := hd.apply_eq_of_tendsto_cocompact z he
  refine ⟨a⁻¹,-b/a,inv_ne_zero ha,?_⟩
  intro z
  have hh := hz z
  field_simp
  linear_combination hh

end CircleDomainRigidity

end

end OAI
