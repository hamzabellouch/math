import OAI.Analysis.CircleDomains.Selection.FixedCircuitExclusion
import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateData
import OAI.Analysis.CircleDomains.Topology.PhysicalCollarCoordinates

namespace OAI

/-! The original masked coordinate has a smooth real lift along each
fixed retained source circuit. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.exists_smooth_circuit_lift
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (hG : IsOpen G)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hsource : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hmask : ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈
      interior (physicalMask π C.mask)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      ∀ t, (v t : UnitAddCircle) = C.physical (Complex.equivRealProdCLM (γ t)) := by
  let D := Complex.equivRealProdCLM ⁻¹'
    (realChartDomain G ∩ interior (physicalMask π C.mask))
  have hD : IsOpen D := ((isOpen_realChartDomain hG).inter isOpen_interior).preimage
    Complex.equivRealProdCLM.continuous
  have hw : SmoothCircleOn (C.physical ∘ Complex.equivRealProdCLM) D := by
    intro z hz a ha
    exact (C.smooth _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  apply exists_smooth_real_circuit_lift hD hw hγ.smooth
  intro t
  refine ⟨?_, hmask _ (hγ.mem_frontier t)⟩
  change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ G
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact hsource (mem_image_of_mem _ (hγ.mem_frontier t))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
