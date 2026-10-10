import OAI.Geometry.NodalSets.Elliptic.PlacedEnvelopeDomains
import OAI.Geometry.NodalSets.Elliptic.SeedNoncriticalPlacement

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem intrinsic_noncritical_envelope_placement : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
    (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
    ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
      (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ ρ : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ → (∀ x, 0 < ρ x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A ρ seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A ρ seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set Coord, IsCompact K → K ⊆ seedCoordPatch r →
      ∀ T : ℝ, SeedEnvelopePlaced (intrinsicSeedCoordMetric A ρ) r a K T := by
  obtain ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,hplace⟩ := seed_coefficient_noncritical_placement
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,?_⟩
  intro A hA hs hp ρ hρ hρp hclose K hK hKP T
  have hc : ContDiff ℝ ∞ (intrinsicChartCoefficient A ρ seedPoint) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact intrinsicChartCoefficient_smoothAt A hA hs hp ρ hρ seedPoint
      (by rw [centeredSphereChart_target]; trivial)
  have hh := hplace (intrinsicChartCoefficient A ρ seedPoint) hc
    (fun y ↦ intrinsicChartCoefficient_positive A hs hp ρ seedPoint
      (by rw [centeredSphereChart_target]; trivial))
    (intrinsicChartCoefficient_symmetric A hs ρ seedPoint)
    (fun y ↦ hρp _) hclose K hK hKP T
  simpa only [intrinsicSeedCoordMetric_eq A hs hp ρ hρp] using hh

theorem intrinsic_noncritical_placed_data : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
    (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
    ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
      (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ ρ : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ → (∀ x, 0 < ρ x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A ρ seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A ρ seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set Coord, IsCompact K → K ⊆ seedCoordPatch r →
      ∀ T : ℝ, Nonempty (PlacedEnvelopeData (intrinsicSeedCoordMetric A ρ) r a K T) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,hplace⟩ := intrinsic_noncritical_envelope_placement
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,?_⟩
  intro A hA hs hp ρ hρ hρp hclose K hK hKP T
  exact (hplace A hA hs hp ρ hρ hρp hclose K hK hKP T).domains

end
end Yau.Target

end OAI
