import OAI.Geometry.RCD.Transport.ResolvedBranchMixture
import OAI.Geometry.RCD.Transport.ResolvedSubplanEntropy
import OAI.Geometry.RCD.Transport.EntropyChordAlgebra

namespace OAI

/-! # Three entropy chords supplied by the actual paired transport law -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem paired_entropy_chords (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] (hσ : σ univ ≠ 0)
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π) (q : Time) :
    let τ₀ := ((σ univ)⁻¹ • σ).map Prod.fst
    let τ₁ := ((σ univ)⁻¹ • σ).map (resolvePathBranch q)
    let τm := (2:ℝ≥0∞)⁻¹ • (τ₀+τ₁)
    EntropyChord (fun t => boltzmannEntropy (hausdorff n X) (τ₀.map (fun γ => γ t)))
      ((|K|/2)*(2*R)^2) ∧
    EntropyChord (fun t => boltzmannEntropy (hausdorff n X) (τ₁.map (fun γ => γ t)))
      ((|K|/2)*(2*R)^2) ∧
    EntropyChord (fun t => boltzmannEntropy (hausdorff n X) (τm.map (fun γ => γ t)))
      ((|K|/2)*(2*R)^2) := by
  have hmass : (σ.map diagonalFirst) univ=σ univ := by
    rw [Measure.map_apply measurable_diagonalFirst MeasurableSet.univ,preimage_univ]
  have hleft : (((σ.map diagonalFirst) univ)⁻¹ • σ.map diagonalFirst).map (resolvePathBranch q)=
      ((σ univ)⁻¹ • σ).map Prod.fst := by
    rw [hmass,Measure.map_smul _ (measurable_resolvePathBranch q).aemeasurable,
      diagonalFirst_resolved,Measure.map_smul _ measurable_fst.aemeasurable]
  have hld : (σ.map diagonalFirst).map Prod.fst ≤ π := by rwa [diagonalFirst_fst]
  have hrd : (σ.map diagonalFirst).map Prod.snd ≤ π := by rwa [diagonalFirst_snd]
  refine ⟨?_,?_,?_⟩
  · intro s t r
    have h := hX.resolved_subplan_entropy_chord hn p hR π hg hp hc hs₀ hs₁
      (σ.map diagonalFirst) (by rwa [hmass]) hld hrd q s t r
    simpa only [hleft] using h
  · exact fun s t r => hX.resolved_subplan_entropy_chord hn p hR π hg hp hc hs₀ hs₁ σ hσ hl hr q s t r
  · intro s t r
    obtain ⟨hlm,hrm⟩ := halfResolvedPair_dominated σ π hl hr
    have h := hX.resolved_subplan_entropy_chord hn p hR π hg hp hc hs₀ hs₁
      (halfResolvedPair σ) (by rwa [halfResolvedPair_mass]) hlm hrm q s t r
    simpa only [normalized_halfResolvedPair] using h

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
