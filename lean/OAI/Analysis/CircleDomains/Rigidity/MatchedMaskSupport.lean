import OAI.Analysis.CircleDomains.Topology.PlaneComponentRelation
import OAI.Analysis.CircleDomains.Rigidity.TraceMaskPrimitive

namespace OAI

/-! A target scalar that vanishes near infinity gives a compact source
mask, with anchor zero. This uses the actual closed end correspondence. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem scalar_zero_near_infty (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {φ : Sphere → ℝ} (hφ : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), φ p = 0) :
    ∀ᶠ q in 𝓝 (OnePoint.infty : Sphere), φ (D.selectedTarget hG hf q) = 0 := by
  obtain ⟨Z,hZsub,hZopen,hZinf⟩ := mem_nhds_iff.mp hφ
  obtain ⟨V,hV,hVinf,hrel⟩ := closed_relation_neighborhood (D.componentRelation_closed hf) hZopen
    (K := {OnePoint.infty}) (by
      intro q hq p hp
      have hq' : q = OnePoint.infty := mem_singleton_iff.mp hq
      subst q
      have he : p = OnePoint.infty := (D.componentRelation_on_domain hinf hp).trans hfix
      exact he.symm ▸ hZinf)
  filter_upwards [hV.mem_nhds (hVinf (mem_singleton _))] with q hq
  exact hZsub (hrel q hq _ (D.selectedTarget_mem hG hf q))

 theorem mask_compactSupport (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {φ : Sphere → ℝ} (hφ : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), φ p = 0)
    (cutoff : ℕ → ℂ → ℝ) (I : ℕ → Set ℝ) :
    HasCompactSupport (fun z => infiniteTracePrimitive cutoff I 0 z
      (φ (D.selectedTarget hG hf (z : Sphere)))) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have hz := OnePoint.tendsto_coe_infty.eventually (D.scalar_zero_near_infty hG hinf hf hfix hφ)
  filter_upwards [hz] with z hz
  simp only [hz,infiniteTracePrimitive,intervalIntegral.integral_same,Pi.zero_apply]

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
