import OAI.Analysis.CircleDomains.Reflection.SphereClosedExteriorInjection
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

/-! The normalized conformal map has an actual homeomorphism on the
compact closed exterior. No boundary correspondence is assumed. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_sphere_closed_exterior_homeomorph {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    ∃e : closure (closedTerminalCap H)ᶜ ≃ₜ (((↑) : ℂ → Sphere) '' closedBall 0 1),
      ∀p, (e p : Sphere)=
        extendFrom (closedTerminalCap H)ᶜ (exteriorDiskNormalization d s hs ∘ f) p := by
  let U := (closedTerminalCap H)ᶜ
  let E := extendFrom U (exteriorDiskNormalization d s hs ∘ f)
  let D := ((↑) : ℂ → Sphere) '' closedBall 0 1
  have hc : ContinuousOn E (closure U) :=
    (analytic_sphere_closed_exterior_extension hH hs hf).1
  have hi : InjOn E (closure U) := analytic_sphere_closed_exterior_injective hH hs hf
  have he : E '' closure U=D := analytic_sphere_closed_exterior_image hH hs hf
  have hb : BijOn E (closure U) D := ⟨fun x hx => he ▸ mem_image_of_mem E hx,
    hi,fun y hy => by rw [←he] at hy; exact hy⟩
  let : CompactSpace (closure U) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let e : closure U ≃ D := Equiv.ofBijective (hb.mapsTo.restrict E (closure U) D) hb.bijective
  have hec : Continuous e := by
    exact hc.mapsToRestrict hb.mapsTo
  exact ⟨hec.homeoOfEquivCompactToT2,fun _ => rfl⟩

end CircleDomainRigidity

end

end OAI
