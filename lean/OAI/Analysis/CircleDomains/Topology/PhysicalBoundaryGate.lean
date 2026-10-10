import OAI.Analysis.CircleDomains.Topology.QuotientOrderedCollar
import OAI.Analysis.CircleDomains.Probability.StartingLawBoundaryGate
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationPushforward
import OAI.Analysis.CircleDomains.Modulus.SphericalChartCost

namespace OAI

/-! The original gate on physical arc starts gives the required lower
bound for the actual physical collar. The inverse quotient map is used
only on its homeomorphic domain. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
 theorem physicalValue_quotient {G U : Set Sphere} (e : G ≃ₜ U) (y₀ : Sphere)
    (π : Sphere → Sphere) (he : ∀ x : G, (e x).val = π x.val) {x : Sphere} (hx : x ∈ G) :
    physicalValue e y₀ (π x) = x := by
  have hp : π x ∈ U := (he ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).property
  have hh : (⟨π x, hp⟩ : U) = e ⟨x, hx⟩ := Subtype.ext (he ⟨x, hx⟩).symm
  simp only [physicalValue, dite_eq_left hp, hh, e.symm_apply_apply]

omit [BorelSpace C(PathTime, Sphere)] in
 theorem compact_startingLaw_physical_gate
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ x : G, (e x).val = π x.val)
    {H J : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H}
    (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hfront : frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)))
    {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (Φ : ℂ → ℝ) (hΦ : Measurable Φ) (d : ℝ)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A), d ≤ Φ (finiteCoord (physicalValue e y₀ (γ.val 0)))) :
    ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K (η.map f) : Measure UnitAddCircle),
      d ≤ Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ))) := by
  let ψ : Sphere → ℝ := fun x => Φ (finiteCoord (physicalValue e y₀ x))
  have hψ : Measurable ψ := hΦ.comp (measurable_finiteCoord.comp (measurable_physicalValue e hU y₀))
  have hg := compact_startingLaw_gate J hb A K η hAS F hF f hf hmap ψ hψ d hgate
  filter_upwards [hg] with θ hθ
  have hident := D.quotient_boundary_identification hπ hfront hb hF θ
  have hx : (D.circuit 0 (D.angle.symm (unitCircleCut θ)) : Sphere) ∈ G := by
    apply hboundary
    simpa only [C.disk_zero] using
      D.circuit_mem_frontier ⟨le_rfl, C.width_pos.le⟩ (D.angle.symm (unitCircleCut θ))
  change d ≤ Φ (finiteCoord (physicalValue e y₀ (centeredJordanBoundary J b θ))) at hθ
  rw [← hident, physicalValue_quotient e y₀ π he hx, finiteCoord_coe] at hθ
  exact hθ

end CircleDomainRigidity

end

end OAI
