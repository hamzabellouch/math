import OAI.Analysis.CircleDomains.Topology.MapDiskExclusion

namespace OAI

/-! The actual assigned mixed limit avoids every retained source test in
the map--disk topology used for countable selection. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem AssignedMixedModelLimit.not_mem_mapDiskExclusion
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (j : C)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (data j).mask))
    (hfiber : π ⁻¹' {σ (data j).singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hp : ∀ t, (v t : UnitAddCircle) = (data j).physical (Complex.equivRealProdCLM (γ t))) :
    (finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉
      mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v ((data j).sourceStokesBudget (5 * M.real.radius)) := by
  exact L.excludes_source_collar hgreen hsch harea hG hinf hπ hclosed H γ hγ hbd hH j
    hmask hfiber v hv hp

end CircleDomainRigidity.FiniteTransfer

end

end OAI
