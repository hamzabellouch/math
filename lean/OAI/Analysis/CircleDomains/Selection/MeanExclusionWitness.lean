import OAI.Analysis.CircleDomains.Selection.MeanCircuitExclusion
import OAI.Analysis.CircleDomains.Topology.MixedMapDiskExclusion

namespace OAI

/-! A constructed mean test retains its actual source curve, mask containment,
singular fiber containment, and the open neighborhood it excludes. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure MeanExclusionWitness {T : Type*} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : T → Sphere} (N : MaskedCoordinateData G U π σ)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℂ) (r : ℝ≥0) (R : ℝ) where
  disk : ℂ ≃ₜ ℂ
  curve : ℝ → ℂ
  regular : PositiveJordanParametrization disk curve
  boundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior disk) ⊆ G
  mask : realChartDomain (closedTerminalCap disk) ⊆ interior (physicalMask π N.mask)
  fiber : π ⁻¹' {σ N.singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior disk
  lift : ℝ → ℝ
  smooth_lift : ContDiff ℝ (⊤ : ℕ∞) lift
  projects : ∀ t, (lift t : UnitAddCircle) = N.physical (Complex.equivRealProdCLM (curve t))
  member : (finiteSourceMap F₀ hF₀, c, r) ∈ mapDiskExclusion
    (sourceCircuit curve regular.smooth.continuous
      (fun t => boundary (mem_image_of_mem _ (regular.mem_frontier t)))) lift (N.sourceStokesBudget R)

namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 def neighborhood : Set (MapDiskData G) := mapDiskExclusion
    (sourceCircuit W.curve W.regular.smooth.continuous
      (fun t => W.boundary (mem_image_of_mem _ (W.regular.mem_frontier t))))
    W.lift (N.sourceStokesBudget R)

 theorem isOpen_neighborhood : IsOpen W.neighborhood :=
  isOpen_mapDiskExclusion _ W.lift W.smooth_lift _

 theorem mem_neighborhood : (finiteSourceMap F₀ hF₀, c, r) ∈ W.neighborhood := W.member

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
