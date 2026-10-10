import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanPhysicalContinuation
import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanParametrization

namespace OAI

/-! Every point of the actual analytic Jordan boundary has a physical
injective germ with the correct exterior side. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma analytic_jordan_boundary_germ {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ))
    {x : ℂ} (hx : x∈frontier (jordanInterior H)) :
    ∃(O:Set ℂ)(G:ℂ→ℂ),IsOpen O ∧ x∈O ∧ DifferentiableOn ℂ G O ∧ InjOn G O ∧
      EqOn G (fun z => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere))))
        (O∩(closure (jordanInterior H))ᶜ) ∧
      ∀z∈O,‖G z‖<1 ↔ z∉closure (jordanInterior H) := by
  obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,he,hfront⟩ := exists_analytic_jordan_parametrization hH
  rw [←hfront] at hx
  obtain ⟨z,hz,hzx⟩ := hx
  let p : ℂ := (z-c)/(r:ℂ)
  have hp : ‖p‖=1 := by
    dsimp only [p]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      mem_sphere_iff_norm.mp hz,div_self hr.ne']
  have hzp : c+(r:ℂ)*p=z := by
    dsimp only [p]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hr.ne' : (r:ℂ)≠0)]
    ring
  have hfα : IsConformalEquivalence f
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ) := by
    simpa only [he,closedTerminalCap] using hf
  obtain ⟨O,G,hO,hpoint,hGd,hGi,hGe,_,hside⟩ :=
    analytic_jordan_physical_continuation_sides hS hα hi hr hs hp hDS hfα
  refine ⟨O,G,hO,?_,hGd,hGi,?_,?_⟩
  · rwa [hzp,hzx] at hpoint
  · simpa only [he] using hGe
  · simpa only [he] using hside

end CircleDomainRigidity

end

end OAI
