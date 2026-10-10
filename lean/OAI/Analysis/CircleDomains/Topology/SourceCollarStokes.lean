import OAI.Analysis.CircleDomains.Selection.PrescribedStokesGeometry
import OAI.Analysis.CircleDomains.Rigidity.RegularMaskedStokes
import OAI.Analysis.CircleDomains.Transfer.RegularImageCircuit

namespace OAI

/-! The numerical source-energy bound on an actual image of a retained
source collar. All target holes and the regular image circuit are derived. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.source_collar_stokes_bound
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hπ : Continuous π) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain)
    (c : T.indices → ℂ) (r : T.indices → ℝ) (hr : ∀ i, 0 ≤ r i)
    (he : ∀ i, connectedComponentIn T.model.domainᶜ (a.point i) =
      ((↑) : ℂ → Sphere) '' closedBall (c i) (r i))
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ i, closedBall (c i) (r i))ᶜ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ openCompletedRegion T.terminals.H)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (C l).mask))
    (s : T.indices) (hsing : (s : S) = (C l).singular)
    (hs : closedTerminalCap (T.terminals.H s) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    {L : ℝ} (hL : 0 ≤ L)
    (hbounded : ∀ J : ℂ ≃ₜ ℂ,
      T.model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) →
      jordanInterior J ⊆ closedBall 0 L) :
    |circleFormIntegral (fun z => infDist z (closedBall (c s) (r s)))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere)))
      (fun t => finiteCoord (T.model.forward (γ t : Sphere)))| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
          fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε) +
      2 * Real.pi * L * (Real.sqrt (∑' t : {t : S // t ≠ (C l).singular},
        ((C l).upper t - (C l).lower t) ^ 2) + ε) := by
  obtain ⟨D, hDc, hDr⟩ := T.exists_stokes_collar_geometry_prescribed hsch l hinf hσB
    H hbd hmask s hs a c r hr he hd hext
  have hp := T.model.equivalence.regular_image_circuit
    (T.core_model (infty_mem_sphericalCore T.core)) T.model.principal.1 hγ hbd D.boundary
  have hb := D.source_stokes_bound_regular hgreen hG hπ hσ hmetric hsing _ hp hL
    (hbounded D.target D.boundary)
  simpa only [hDc, hDr] using hb

end CircleDomainRigidity.FiniteTransfer

end

end OAI
