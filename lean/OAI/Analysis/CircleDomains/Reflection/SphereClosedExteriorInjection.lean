import OAI.Analysis.CircleDomains.Reflection.SphereClosedExteriorCoordinates

namespace OAI

/-! Global injectivity of the actual spherical closed-exterior extension,
including the point at infinity. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma analytic_sphere_closed_exterior_injective {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    InjOn (extendFrom (closedTerminalCap H)ᶜ (exteriorDiskNormalization d s hs ∘ f))
      (closure (closedTerminalCap H)ᶜ) := by
  let U := (closedTerminalCap H)ᶜ
  let F := exteriorDiskNormalization d s hs ∘ f
  let E := extendFrom U F
  let A := (closure (jordanInterior H))ᶜ
  let g := fun z : ℂ => finiteCoord (F (z : Sphere))
  let e := extendFrom A g
  change InjOn E (closure U)
  obtain ⟨_,hEe⟩ := analytic_sphere_closed_exterior_extension hH hs hf
  change EqOn E F U at hEe
  have hF := hf.trans (isConformalEquivalence_exteriorDiskNormalization d hs)
  have hb {p:Sphere} (hp:p∈closure U) (hn:p∉U) :
      ∃z:ℂ,p=(z:Sphere) ∧ z∈frontier (jordanInterior H) := by
    have hpH : p∈closedTerminalCap H := not_not.mp hn
    obtain ⟨z,hz,rfl⟩ := hpH
    refine ⟨z,rfl,?_⟩
    rw [(jordanInterior_isOpen H).frontier_eq]
    refine ⟨hz,?_⟩
    have hzo : z∈closure A := coe_mem_closed_jordan_exterior.mp hp
    simpa only [A,closure_compl,interior_closure_jordanInterior,mem_compl_iff] using hzo
  have hbn {p:Sphere} (hp:p∈closure U) (hn:p∉U) : ‖finiteCoord (E p)‖=1 := by
    obtain ⟨z,rfl,hz⟩ := hb hp hn
    have hze := sphere_plane_closed_exterior_eq hH hs hf
      (coe_mem_closed_jordan_exterior.mp hp)
    change E (z : Sphere)=(e z : Sphere) at hze
    rw [hze,finiteCoord_coe]
    exact analytic_jordan_closed_exterior_boundary_norm hH hs hf hz
  have hin {p:Sphere} (hp:p∈U) : ‖finiteCoord (E p)‖<1 := by
    obtain ⟨z,hz,he⟩ := hF.2.1 hp
    change (z : Sphere)=F p at he
    rw [hEe hp,←he,finiteCoord_coe]
    exact mem_ball_zero_iff.mp hz
  intro p hp q hq heq
  by_cases hpu : p∈U
  · by_cases hqu : q∈U
    · apply hF.bijOn.injOn hpu hqu
      rwa [hEe hpu,hEe hqu] at heq
    · have hlt := hin hpu
      rw [heq,hbn hq hqu] at hlt
      exact (lt_irrefl _ hlt).elim
  · by_cases hqu : q∈U
    · have hlt := hin hqu
      rw [←heq,hbn hp hpu] at hlt
      exact (lt_irrefl _ hlt).elim
    · obtain ⟨x,rfl,_⟩ := hb hp hpu
      obtain ⟨y,rfl,_⟩ := hb hq hqu
      have hx := coe_mem_closed_jordan_exterior.mp hp
      have hy := coe_mem_closed_jordan_exterior.mp hq
      have hxi := sphere_plane_closed_exterior_eq hH hs hf hx
      have hyi := sphere_plane_closed_exterior_eq hH hs hf hy
      change E (x:Sphere)=(e x:Sphere) at hxi
      change E (y:Sphere)=(e y:Sphere) at hyi
      rw [hxi,hyi] at heq
      have he : e x=e y := OnePoint.coe_injective heq
      exact congrArg ((↑) : ℂ → Sphere)
        (analytic_jordan_closed_exterior_injective hH hs hf hx hy he)

end CircleDomainRigidity

end

end OAI
