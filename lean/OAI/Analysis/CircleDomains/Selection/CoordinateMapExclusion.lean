import OAI.Analysis.CircleDomains.Topology.MapDiskExclusion

namespace OAI

/-! A fixed actual masked coordinate defines an open excluded neighborhood
in map--disk space whenever its boundary integral exceeds its source budget. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.exists_mapDisk_exclusion
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (hG : IsOpen G)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π C.mask))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℂ) (r : ℝ≥0) (R : ℝ)
    (hlower : C.sourceStokesBudget R < |circleFormIntegral
      (fun z => Metric.infDist (F z) (Metric.closedBall c (r : ℝ)))
      (C.physical ∘ Complex.equivRealProdCLM) γ|) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, (v t : UnitAddCircle) = C.physical (Complex.equivRealProdCLM (γ t))) ∧
      IsOpen (mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R)) ∧
      (finiteSourceMap F hF, c, r) ∈ mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R) := by
  let W := Complex.equivRealProdCLM ⁻¹' (realChartDomain G ∩ interior (physicalMask π C.mask))
  have hW : IsOpen W := ((isOpen_realChartDomain hG).inter isOpen_interior).preimage
    Complex.equivRealProdCLM.continuous
  have hγW : ∀ t, γ t ∈ W := by
    intro t
    refine ⟨?_, ?_⟩
    · change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ G
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hbd (mem_image_of_mem _ (hγ.mem_frontier t))
    · apply hmask
      change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
        closedTerminalCap H
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact mem_image_of_mem _ (frontier_subset_closure (hγ.mem_frontier t))
  have hw : SmoothCircleOn (C.physical ∘ Complex.equivRealProdCLM) W := by
    intro z hz a ha
    exact (C.smooth _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  have hFW : ContinuousOn F W := hF.mono (by
    intro z hz
    have hzG := hz.1
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ G at hzG
    rw [ContinuousLinearEquiv.symm_apply_apply] at hzG
    change (z : Sphere) ∈ G
    exact hzG)
  obtain ⟨v, hv, hp, _, hmem⟩ := exists_open_fixed_circuit_exclusion hW hw hγ.smooth hγW
    F hFW c r (C.sourceStokesBudget R) hlower
  refine ⟨v, hv, hp, isOpen_mapDiskExclusion _ v hv _, ?_⟩
  exact hmem

end CircleDomainRigidity.FiniteTransfer

end

end OAI
