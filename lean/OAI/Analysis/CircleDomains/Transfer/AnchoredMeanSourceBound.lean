import OAI.Analysis.CircleDomains.Selection.RecursiveMeanExclusion
import OAI.Analysis.CircleDomains.Selection.MeanExclusionRadius
import OAI.Analysis.CircleDomains.Selection.ExteriorZeroAnchor

namespace OAI

/-! The retained inner mean circuit stays outside the fixed endpoint
anchor. Its physical radius is therefore bounded before the final model
radius is chosen. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem RecursiveMeanOutput.boundary_norm_lt_of_anchor
    {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} {L : RecursiveCodeLaw base π Flags ω}
    {J : ℂ ≃ₜ ℂ} {ε : ℝ≥0∞}
    {Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J) ε}
    {F₀ : ℂ → ℂ} {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)}
    {c : ℂ} {r : NNReal} {R δ : ℝ} (N : RecursiveMeanOutput hsch Q F₀ hF₀ c r R δ)
    (hanchor : Disjoint base.anchor (((↑) : ℂ → Sphere) '' jordanInterior J))
    {B : ℝ} (hB : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
    ∀ z ∈ _root_.frontier (jordanInterior N.exclusion.disk), ‖z‖ < B := by
  apply N.exclusion.boundary_norm_lt
  intro z hz hm
  have hmask : π (z : Sphere) ∈ N.mask := by
    rwa [N.mask_eq] at hm
  exact disjoint_left.mp hanchor (hB z hz) (N.inner hmask)

end CircleDomainRigidity

end

end OAI
