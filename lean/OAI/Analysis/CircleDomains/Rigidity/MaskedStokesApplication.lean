import OAI.Analysis.CircleDomains.Rigidity.MaskedStokesGeometry

namespace OAI

/-! Stokes on the constructed collar geometry of the actual masked model. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem StokesCollarGeometry.source_stokes_bound
    (hgreen : FiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    {T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀} {l : Fin n}
    {s : T.indices} {H : ℂ ≃ₜ ℂ}
    {a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain}
    (D : StokesCollarGeometry T l s H a)
    (hG : IsOpen G) (hπ : Continuous π) (hσ : Injective σ)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p)
    (hsing : (s : S) = (C l).singular)
    (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization D.target γ)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior D.target ⊆ closedBall 0 L) :
    |circleFormIntegral (fun z => infDist z (closedBall (D.center s) (D.radius s)))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
          fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε) +
      2 * Real.pi * L *
        (Real.sqrt (∑' t : {t : S // t ≠ (C l).singular},
          ((C l).upper t - (C l).lower t) ^ 2) + ε) := by
  have hb := T.source_stokes_bound hgreen hG hπ hσ hmetric l a
    D.center D.radius D.radius_nonneg D.disjoint D.exterior
    (fun i => D.disks i ▸ Subset.rfl) D.count D.label D.injective D.base
    (by rw [D.distinguished]; exact hsing) D.mask D.target γ hγ D.inside D.region hL hbounded
  simpa only [D.distinguished] using hb

end CircleDomainRigidity.FiniteTransfer

end

end OAI
