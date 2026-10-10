import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanCollarApplication
import OAI.Analysis.CircleDomains.Topology.PhysicalBoundaryGate

namespace OAI

/-! The full boundary side of the law alternative. The original physical
start gate supplies the lower bound, its point-avoidance supplies the
atomless boundary law, and the actual smoothed mean data supplies the
smooth circle coordinate. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_gated_mean_collar_lower_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (G U S M : Set Sphere) (e : G ≃ₜ U)
    (hG : IsOpen G) (hU : IsOpen U) (hS : IsOpen S) (y₀ : Sphere)
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
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (η.map Subtype.val) x = 0)
    (O : Set ℂ) (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦm : Measurable Φ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O)
    {d : ℝ} (hd : 0 < d)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A), d ≤ Φ (finiteCoord (physicalValue e y₀ (γ.val 0)))) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π,
      (∀ x, |Q.error x| ≤ ε) →
      (∀ t, (D.circuit ρ t : Sphere) ∈ G ∧ π (D.circuit ρ t : Sphere) ∈ S) →
      (∀ t, ∀ᵐ α : K ∂(η.map f : Measure K), F (π (D.circuit ρ t : Sphere)) ∉ range α.val) →
      d / 2 < |circleFormIntegral Φ Q.physical (C.curve ρ)| := by
  let := compact_startingLaw_atomless J hb A K η hAS F hF f hf hmap havoid
  have hgate' := compact_startingLaw_physical_gate e hU y₀ π hπ he hboundary hfront hb
    F hF D A K η hAS f hf hmap Φ hΦm d hgate
  exact exists_smooth_mean_collar_lower_bound hsch hsep K hK hKS (η.map f)
    G U S M hG hS b π hπ (fun x hx => (he ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).property)
    F D O hO hCO Φ hΦ hd hgate'

end CircleDomainRigidity

end

end OAI
