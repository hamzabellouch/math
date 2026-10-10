import OAI.Analysis.CircleDomains.Topology.GatedMeanCollar

namespace OAI

/-! The collar tolerance and depth are selected before a period mask is chosen.
This follows from the same physical strict lower bound, whose estimates do not use
the mask. It allows an inner mask to enclose the chosen integration curve. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
 theorem exists_smooth_mean_collar_lower_bound_all_masks
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (G U S : Set Sphere) (hG : IsOpen G) (hS : IsOpen S) (b : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (hπU : ∀ x ∈ G, π x ∈ U)
    (F : C(Sphere, ℂ))
    {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H}
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (O : Set ℂ) (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O)
    {d : ℝ} (hd : 0 < d)
    (hgate : ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
      d ≤ Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ)))) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ (M : Set Sphere) (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π),
      (∀ x, |Q.error x| ≤ ε) →
      (∀ t, (D.circuit ρ t : Sphere) ∈ G ∧ π (D.circuit ρ t : Sphere) ∈ S) →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), F (π (D.circuit ρ t : Sphere)) ∉ range α.val) →
      d / 2 < |circleFormIntegral Φ Q.physical (C.curve ρ)| := by
  obtain ⟨ε, hε, hε1, σ, hσ, hσw, hbound⟩ :=
    D.exists_strict_mean_lower_bound hsch hsep K hK hKS η O hO hCO Φ hΦ hd hgate
  refine ⟨ε, hε, hε1, σ, hσ, hσw, ?_⟩
  intro ρ hρ M Q herror hcurve hmiss
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S
  have hW : IsOpen W := (hG.preimage OnePoint.continuous_coe).inter
    (hS.preimage (hπ.comp OnePoint.continuous_coe))
  have hρC : ρ ∈ Icc (0 : ℝ) C.width :=
    ⟨hρ.1.le, hρ.2.trans (hσw.le.trans D.width_le)⟩
  have hRc : Continuous (fun t => Q.error (π (D.circuit ρ t : Sphere))) := by
    apply Q.error_continuous.comp_continuous
      (hπ.comp (OnePoint.continuous_coe.comp (D.circuit_smooth hρC).continuous))
    intro t
    exact ⟨hπU _ (hcurve t).1, (hcurve t).2⟩
  exact hbound ρ hρ W hW Q.physical Q.physical_smooth hcurve hmiss
    (fun z => Q.error (π (z : Sphere))) hRc
    (fun t => Q.physical_value _ (hcurve t).1 (hcurve t).2)
    (fun t _ => herror _)

 theorem exists_gated_mean_collar_lower_bound_all_masks
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (G U S : Set Sphere) (e : G ≃ₜ U)
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
      ∀ (M : Set Sphere) (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π),
      (∀ x, |Q.error x| ≤ ε) →
      (∀ t, (D.circuit ρ t : Sphere) ∈ G ∧ π (D.circuit ρ t : Sphere) ∈ S) →
      (∀ t, ∀ᵐ α : K ∂(η.map f : Measure K), F (π (D.circuit ρ t : Sphere)) ∉ range α.val) →
      d / 2 < |circleFormIntegral Φ Q.physical (C.curve ρ)| := by
  let := compact_startingLaw_atomless J hb A K η hAS F hF f hf hmap havoid
  have hgate' := compact_startingLaw_physical_gate e hU y₀ π hπ he hboundary hfront hb
    F hF D A K η hAS f hf hmap Φ hΦm d hgate
  exact exists_smooth_mean_collar_lower_bound_all_masks hsch hsep K hK hKS (η.map f)
    G U S hG hS b π hπ (fun x hx => (he ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).property)
    F D O hO hCO Φ hΦ hd hgate'

end CircleDomainRigidity

end

end OAI
