import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanPhysicalContinuation
import OAI.Analysis.CircleDomains.Reflection.LocalBoundaryExtension

namespace OAI

/-! A one-hole circularization has an actual continuous extension to
the closed exterior when its Jordan boundary is analytic. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma analytic_jordan_closed_exterior_extension {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    let A := (closure (jordanInterior H))ᶜ
    let g := fun z : ℂ => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))
    ContinuousOn (extendFrom A g) (closure A) ∧ EqOn (extendFrom A g) g A := by
  dsimp only
  let A := (closure (jordanInterior H))ᶜ
  let g := fun z : ℂ => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))
  let US := (closedTerminalCap H)ᶜ
  have hUS : IsOpen US := (isCompact_closedTerminalCap H).isClosed.isOpen_compl
  have hA : IsOpen A := isClosed_closure.isOpen_compl
  have hnorm := hf.trans (isConformalEquivalence_exteriorDiskNormalization d hs)
  have hg : DifferentiableOn ℂ g A := by
    intro z hz
    have hzU : (z : Sphere)∈US := by
      rintro ⟨w,hw,he⟩
      exact hz (OnePoint.coe_injective he ▸ hw)
    have hn : exteriorDiskNormalization d s hs (f (z : Sphere))≠∞ := by
      obtain ⟨w,_,he⟩ := hnorm.2.1 hzU
      change (w : Sphere)=exteriorDiskNormalization d s hs (f (z : Sphere)) at he
      rw [←he]
      exact OnePoint.coe_ne_infty w
    exact (analyticAt_finite_map_of_conformal hUS hnorm.1 hzU hn).differentiableAt.differentiableWithinAt
  have hlocal : ∀x∈closure A,∃(O:Set ℂ)(G:ℂ→ℂ),
      IsOpen O ∧ x∈O ∧ ContinuousOn G O ∧ EqOn G g (O∩A) := by
    intro x hx
    by_cases hxA : x∈A
    · exact ⟨A,g,hA,hxA,hg.continuousOn,fun _ _ => rfl⟩
    have hxcl : x∈closure (jordanInterior H) := not_not.mp hxA
    have hxout : x∉jordanInterior H := by
      simpa only [A,closure_compl,interior_closure_jordanInterior,mem_compl_iff] using hx
    have hxfront : x∈frontier (jordanInterior H) := by
      rw [(jordanInterior_isOpen H).frontier_eq]
      exact ⟨hxcl,hxout⟩
    obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,he,hfront⟩ := exists_analytic_jordan_parametrization hH
    rw [←hfront] at hxfront
    obtain ⟨z,hz,hzx⟩ := hxfront
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
    obtain ⟨O,G,hO,hpoint,hGd,_,hGe,_⟩ :=
      analytic_jordan_physical_continuation hS hα hi hr hs hp hDS hfα
    refine ⟨O,G,hO,?_,hGd.continuousOn,?_⟩
    · rwa [hzp,hzx] at hpoint
    · simpa only [g,A,he] using hGe
  exact ⟨continuousOn_extendFrom_of_local_extensions (Subset.refl _) hlocal,
    extendFrom_extends hg.continuousOn⟩

end CircleDomainRigidity

end

end OAI
