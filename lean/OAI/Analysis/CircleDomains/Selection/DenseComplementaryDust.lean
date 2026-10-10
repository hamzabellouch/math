import OAI.Analysis.CircleDomains.Modulus.NormalizedComponentQuotient
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! A totally disconnected subset of the sphere has empty interior. This supplies
actual density of the component quotient domain in the countable selection. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem dense_compl_of_totallyDisconnected_sphere {D : Set Sphere}
    (hD : IsTotallyDisconnected D) : Dense Dᶜ := by
  apply dense_iff_inter_open.mpr
  intro W hW hne
  by_contra h
  have hWD : W ⊆ D := by
    intro x hx
    by_contra hxD
    exact h ⟨x, hx, hxD⟩
  have hd : Dense (range ((↑) : ℂ → Sphere)) := OnePoint.denseRange_coe
  obtain ⟨p, ⟨z, rfl⟩, hp⟩ := hd.exists_mem_open hW hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hW.preimage OnePoint.continuous_coe) z hp
  have hsub := hD (((↑) : ℂ → Sphere) '' Metric.ball z r)
    (by rintro _ ⟨w, hw, rfl⟩; exact hWD (hball hw))
    (((convex_ball z r).isPreconnected).image _ OnePoint.continuous_coe.continuousOn)
  have hs : (Metric.ball z r).Subsingleton := by
    intro x hx y hy
    exact OnePoint.coe_injective (hsub ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  have heq : Metric.ball z r = {z} :=
    Set.Subset.antisymm (fun w hw => hs hw (Metric.mem_ball_self hr))
      (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  exact not_isOpen_singleton z (heq ▸ Metric.isOpen_ball)

end CircleDomainRigidity

end

end OAI
