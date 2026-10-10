import OAI.Analysis.CircleDomains.Selection.RestrictedMeanExclusion

namespace OAI

/-! A fixed mean exclusion remains valid for every smaller target-radius
budget. This permits an open radius interval in the common selection space. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem FiniteTransfer.MaskedCoordinateData.sourceStokesBudget_mono
    {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    (N : MaskedCoordinateData G U π σ) : Monotone N.sourceStokesBudget := by
  intro R R' hR
  unfold MaskedCoordinateData.sourceStokesBudget
  gcongr

namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem boundary_in_mask (z : ℂ) (hz : z ∈ frontier (jordanInterior W.disk)) :
    π (z : Sphere) ∈ N.mask := by
  have hx : Complex.equivRealProdCLM z ∈ realChartDomain (closedTerminalCap W.disk) := by
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ closedTerminalCap W.disk
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ (frontier_subset_closure hz)
  have hm := interior_subset (W.mask hx)
  change π ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ N.mask at hm
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm

 theorem boundary_norm_lt {B : ℝ}
    (hB : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∉ N.mask) :
    ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B := by
  intro z hz
  by_contra hn
  exact hB z (not_lt.mp hn) (W.boundary_in_mask z hz)

 def smallerRadius {R' : ℝ} (hR : R' ≤ R) : MeanExclusionWitness N F₀ hF₀ c r R' where
  disk := W.disk
  curve := W.curve
  regular := W.regular
  boundary := W.boundary
  mask := W.mask
  fiber := W.fiber
  lift := W.lift
  smooth_lift := W.smooth_lift
  projects := W.projects
  member := (N.sourceStokesBudget_mono hR).trans_lt W.member

 theorem neighborhood_subset_smallerRadius {R' : ℝ} (hR : R' ≤ R) :
    W.neighborhood ⊆ (W.smallerRadius hR).neighborhood :=
  fun _ hp => (N.sourceStokesBudget_mono hR).trans_lt hp

 theorem not_mem_of_radius_le
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {J : Type*} [LinearOrder J] {d : CountableRealCoordinates G π σ}
    {data : J → MaskedCoordinateData G d.source π σ} {retained : ℕ → J} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hU : d.source = U) (j : J) (hN : HEq (data j) N)
    (hsize : 5 * M.real.radius ≤ R)
    (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * M.real.radius) :
    (finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉ W.neighborhood := by
  have hnot := (W.smallerRadius hsize).not_mem_neighborhood hgreen hsch harea L
    hG hinf hπ hclosed hU j hN rfl hbound
  exact fun hp => hnot (W.neighborhood_subset_smallerRadius hsize hp)

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
