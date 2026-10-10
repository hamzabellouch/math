import OAI.Analysis.CircleDomains.Topology.LimitSphereExtension

namespace OAI

/-! Principal normalization is stable under composition. This uses the
actual decay estimate, without any uniformization hypothesis. -/
open Set Function Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma principal_remainder_comp {F G : ℂ → ℂ}
    (hF : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹))
    (hG : (fun z => G z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    (fun z => G (F z)-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  have ht := (principal_remainder_tendsto_zero hF).mul
    (tendsto_inv₀_cobounded (α := ℂ))
  have hratio : Tendsto (fun z => F z/z) (cobounded ℂ) (𝓝 1) := by
    have h := ht.add_const 1
    simp only [zero_mul, zero_add] at h
    apply h.congr'
    filter_upwards [hn] with z hz
    field_simp
    ring
  have hi : (fun z => (F z)⁻¹) =O[cobounded ℂ] (fun z => z⁻¹) := by
    apply isBigO_of_div_tendsto_nhds
      (hn.mono (fun z hz he => (hz (inv_eq_zero.mp he)).elim)) (1 : ℂ)
    change Tendsto (fun z => (F z)⁻¹ / z⁻¹) (cobounded ℂ) (𝓝 1)
    simpa only [inv_div, inv_one, Pi.div_apply, div_inv_eq_mul, div_eq_mul_inv,
      Pi.inv_apply, mul_inv_rev, inv_inv, mul_comm] using hratio.inv₀ one_ne_zero
  have h := ((hG.comp_tendsto (principal_tendsto_cobounded hF)).trans hi).add hF
  exact h.congr_left (fun z => by dsimp only [Function.comp_apply]; ring)

lemma IsPrincipalNormalized.comp {f g : Sphere → Sphere}
    (hg : IsPrincipalNormalized g) (hf : IsPrincipalNormalized f) :
    IsPrincipalNormalized (g ∘ f) := by
  refine ⟨by simp only [Function.comp_apply,hf.1,hg.1], ?_⟩
  have h := principal_remainder_comp hf.2 hg.2
  have hn : ∀ᶠ z : ℂ in cobounded ℂ, finiteCoord (f (z : Sphere)) ≠ 0 :=
    (principal_tendsto_cobounded hf.2).eventually (show ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 from by
      rw [Metric.cobounded_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact)
  apply h.congr'
  · filter_upwards [hn] with z hz
    have hfin : f (z : Sphere) ≠ ∞ := by
      intro he
      apply hz
      rw [he]
      rfl
    rw [coe_finiteCoord hfin]
    rfl
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end CircleDomainRigidity

end

end OAI
