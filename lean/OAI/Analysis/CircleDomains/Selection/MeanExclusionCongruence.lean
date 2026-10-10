import OAI.Analysis.CircleDomains.Selection.MeanExclusionWitness

namespace OAI

/-! The open exclusion depends only on the source map on its domain.
A measurable extension outside that domain does not change the test. -/
open Set Function
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness

 def congr_map {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ F₁ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)}
    {hF₁ : ContinuousOn F₁ (((↑) : ℂ → Sphere) ⁻¹' G)}
    {c : ℂ} {r : ℝ≥0} {R : ℝ} (W : MeanExclusionWitness N F₀ hF₀ c r R)
    (hEq : EqOn F₀ F₁ (((↑) : ℂ → Sphere) ⁻¹' G)) :
    MeanExclusionWitness N F₁ hF₁ c r R where
  disk := W.disk
  curve := W.curve
  regular := W.regular
  boundary := W.boundary
  mask := W.mask
  fiber := W.fiber
  lift := W.lift
  smooth_lift := W.smooth_lift
  projects := W.projects
  member := by
    have hmaps : finiteSourceMap F₀ hF₀ = finiteSourceMap F₁ hF₁ := by
      ext x
      exact hEq x.property
    rw [← hmaps]
    exact W.member

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
