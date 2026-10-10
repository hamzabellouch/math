import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateStage

namespace OAI

/-! A terminal inside a physical mask has its original quotient label in
that mask. Nonempty label fibers are supplied by the component quotient. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.label_mem_mask_of_terminal_inside
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n)
    (hinf : OnePoint.infty ∈ G) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (H : ℂ ≃ₜ ℂ)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (s : T.indices)
    (hs : closedTerminalCap (T.terminals.H s) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    σ s ∈ (C l).mask := by
  obtain ⟨p, hp, hps⟩ := hσB s
  have hpinf : p ≠ OnePoint.infty := fun he => hp (he ▸ hinf)
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hpinf
  have hz : z ∈ jordanInterior (T.terminals.H s) := T.terminals.fiber_subset s hps
  have hzH := hs (show (z : Sphere) ∈ closedTerminalCap (T.terminals.H s) from
    ⟨z, subset_closure hz, rfl⟩)
  have hzH' : z ∈ jordanInterior H := OnePoint.coe_injective.mem_set_image.mp hzH
  have hm := interior_subset (hmask (show Complex.equivRealProdCLM z ∈
      realChartDomain (closedTerminalCap H) from by
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ closedTerminalCap H
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨z, subset_closure hzH', rfl⟩))
  change π ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈
    (C l).mask at hm
  simpa only [ContinuousLinearEquiv.symm_apply_apply, hps] using hm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
