import OAI.Analysis.CircleDomains.Topology.PrincipalHomeomorphOrientation
import OAI.Analysis.CircleDomains.Selection.PrincipalMobiusIdentity
import OAI.Analysis.CircleDomains.Uniformization.ConformalEqOn

namespace OAI

/-! A normalized homeomorphic conformal extension across a removable
complement is the identity. All normalization and orientation properties
are derived from the extension and its prescribed exterior germ. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_normalized_extension {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) {f g : Sphere → Sphere}
    (hf : IsPrincipalNormalized f) (he : EqOn g f G) : IsPrincipalNormalized g := by
  refine ⟨(he hinf).trans hf.1, ?_⟩
  apply hf.2.congr' _ EventuallyEq.rfl
  have hm := OnePoint.tendsto_coe_infty (hG.mem_nhds hinf)
  change {z : ℂ | (z : Sphere) ∈ G} ∈ Filter.coclosedCompact ℂ at hm
  rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at hm
  filter_upwards [hm] with z hz
  rw [he hz]

 theorem removable_normalized_extension_eq_id {G : Set Sphere}
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hrem : IsConformallyRemovable Gᶜ) {f : Sphere → Sphere}
    (hf : IsConformalOn f G) (hnorm : IsPrincipalNormalized f)
    (H : Sphere ≃ₜ Sphere) (he : EqOn H f G) : ∀ p, H p = p := by
  have hH := principal_normalized_extension hG hinf hnorm he
  have hconf : IsConformalOn H Gᶜᶜ := by
    rw [compl_compl]
    exact hf.congr_eqOn hG he
  obtain ⟨M,hM⟩ := hrem.2 H (principal_homeomorph_orientation H hH) hconf
  have hn : IsPrincipalNormalized (fun p : Sphere => M • p) := by
    have heq : (fun p : Sphere => M • p) = H := funext (fun p => (hM p).symm)
    rw [heq]
    exact hH
  exact fun p => (hM p).trans (principal_mobius_identity M hn p)

end CircleDomainRigidity

end

end OAI
