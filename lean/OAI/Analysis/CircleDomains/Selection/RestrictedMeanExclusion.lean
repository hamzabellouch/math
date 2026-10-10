import OAI.Analysis.CircleDomains.Selection.MeanExclusionWitness
import OAI.Analysis.CircleDomains.Selection.RestrictedCoordinateMarks

namespace OAI

/-! Restricting to the common countable marks preserves a mean exclusion.
Its source budget can only decrease, so the original open neighborhood
remains excluded by a mixed limit retaining that coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 def restrictMarks (A : Set T) (hsing : N.singular ∈ A)
    (hsupport : ∀ s, N.upper s - N.lower s ≠ 0 → s ∈ A) (hR : 0 ≤ R) :
    MeanExclusionWitness (N.restrictMarks A hsing hsupport) F₀ hF₀ c r R where
  disk := W.disk
  curve := W.curve
  regular := W.regular
  boundary := W.boundary
  mask := W.mask
  fiber := W.fiber
  lift := W.lift
  smooth_lift := W.smooth_lift
  projects := W.projects
  member := (N.restrictMarks_sourceStokesBudget_le A hsing hsupport hR).trans_lt W.member

 theorem neighborhood_subset_restrictMarks (A : Set T) (hsing : N.singular ∈ A)
    (hsupport : ∀ s, N.upper s - N.lower s ≠ 0 → s ∈ A) (hR : 0 ≤ R) :
    W.neighborhood ⊆ (W.restrictMarks A hsing hsupport hR).neighborhood := by
  intro p hp
  exact (N.restrictMarks_sourceStokesBudget_le A hsing hsupport hR).trans_lt hp

 theorem not_mem_neighborhood
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {J : Type*} [LinearOrder J] {d : CountableRealCoordinates G π σ}
    {data : J → MaskedCoordinateData G d.source π σ} {retained : ℕ → J} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hU : d.source = U) (j : J) (hN : HEq (data j) N)
    (hsize : R = 5 * M.real.radius)
    (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * M.real.radius) :
    (finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉ W.neighborhood := by
  subst U
  cases eq_of_heq hN
  subst R
  exact L.not_mem_mapDiskExclusion hgreen hsch harea hG hinf hπ hclosed
    W.disk W.curve W.regular W.boundary hbound j W.mask W.fiber W.lift W.smooth_lift W.projects

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
