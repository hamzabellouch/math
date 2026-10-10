import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanBoundaryInjection
import OAI.Analysis.CircleDomains.Topology.ClosedJordanCore

namespace OAI

/-! The continuous closed-exterior extension on the compact sphere,
including the original point at infinity. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma analytic_sphere_closed_exterior_extension {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    let U := (closedTerminalCap H)ᶜ
    let F := exteriorDiskNormalization d s hs ∘ f
    ContinuousOn (extendFrom U F) (closure U) ∧ EqOn (extendFrom U F) F U := by
  dsimp only
  let U := (closedTerminalCap H)ᶜ
  let F := exteriorDiskNormalization d s hs ∘ f
  have hU : IsOpen U := (isCompact_closedTerminalCap H).isClosed.isOpen_compl
  have hF := hf.trans (isConformalEquivalence_exteriorDiskNormalization d hs)
  have hFin : ∀p∈U,F p≠∞ := by
    intro p hp
    obtain ⟨z,_,he⟩ := hF.2.1 hp
    change (z : Sphere)=F p at he
    rw [←he]
    exact OnePoint.coe_ne_infty z
  have hl : ∀p∈closure U,∃(O:Set Sphere)(G:Sphere→Sphere),
      IsOpen O ∧ p∈O ∧ ContinuousOn G O ∧ EqOn G F (O∩U) := by
    intro p hp
    by_cases hpU : p∈U
    · exact ⟨U,F,hU,hpU,fun q hq => (hF.1 q hq).1.continuousWithinAt,fun _ _ => rfl⟩
    have hpH : p∈closedTerminalCap H := not_not.mp hpU
    obtain ⟨x,hx,rfl⟩ := hpH
    have hxo : x∉jordanInterior H := by
      change (x : Sphere)∈closure ((closedTerminalCap H)ᶜ) at hp
      rw [closure_compl,interior_closedTerminalCap] at hp
      intro hxi
      exact hp ⟨x,hxi,rfl⟩
    have hxf : x∈frontier (jordanInterior H) := by
      rw [(jordanInterior_isOpen H).frontier_eq]
      exact ⟨hx,hxo⟩
    obtain ⟨O,G,hO,hxO,hGd,hGi,hGe,_⟩ := analytic_jordan_boundary_germ hH hs hf hxf
    let OS := ((↑) : ℂ → Sphere) '' O
    have hOS : IsOpen OS := OnePoint.isOpen_image_coe.mpr hO
    have hGc : ContinuousOn (extendAtInfinity G) OS := by
      rintro _ ⟨z,hz,rfl⟩
      exact (isConformalAt_extendAtInfinity_coe
        ((hGd z hz).differentiableAt (hO.mem_nhds hz))
        (holomorphicInjOn_deriv_ne_zero hO hGd hGi hz)).1.continuousWithinAt
    refine ⟨OS,extendAtInfinity G,hOS,⟨x,hxO,rfl⟩,hGc,?_⟩
    rintro _ ⟨⟨z,hz,rfl⟩,hzU⟩
    have hzA : z∉closure (jordanInterior H) := fun h => hzU ⟨z,h,rfl⟩
    change (G z : Sphere)=F (z : Sphere)
    rw [hGe ⟨hz,hzA⟩]
    exact coe_finiteCoord (hFin _ hzU)
  exact ⟨continuousOn_extendFrom_of_local_extensions (Subset.refl _) hl,
    extendFrom_extends (fun q hq => (hF.1 q hq).1.continuousWithinAt)⟩

end CircleDomainRigidity

end

end OAI
