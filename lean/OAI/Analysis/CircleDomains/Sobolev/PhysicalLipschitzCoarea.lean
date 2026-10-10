import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoareaTransport
import OAI.Analysis.CircleDomains.Sobolev.LipschitzScalarCoarea

namespace OAI

/-! Exact weighted coarea for a Lipschitz function on the physical
Euclidean plane, with the norm of its actual differential. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

def PhysicalWeightedCoareaIdentity (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) : Prop :=
  AEMeasurable (sobolevLevelIntegral E u q) volume ∧
    (∫⁻ t, sobolevLevelIntegral E u q t) =
      ∫⁻ x in E, q x * ENNReal.ofReal ‖fderiv ℝ u x‖

lemma physical_lipschitz_weighted_coarea {u : EuclideanPlane → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {E : Set EuclideanPlane} (hE : MeasurableSet E)
    (hb : IsBounded E) {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q) :
    PhysicalWeightedCoareaIdentity E u q := by
  have hF : LipschitzWith L (u ∘ complexPlaneCoordinates.symm) := by
    have he : (complexPlaneLinearIsometry.symm : ℂ → EuclideanPlane) = complexPlaneCoordinates.symm := rfl
    simpa only [he,mul_one] using hu.comp complexPlaneLinearIsometry.symm.lipschitz
  have hEc : MeasurableSet (complexPlaneCoordinates '' E) :=
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding.measurableSet_image' hE
  have hEb : IsBounded (complexPlaneCoordinates '' E) :=
    complexPlaneLinearIsometry.lipschitz.isBounded_image hb
  obtain ⟨hm,he⟩ := lipschitz_scalar_weighted_coarea hF hEc hEb
    (hq.comp complexPlaneCoordinates.symm.continuous.measurable)
  have hlevels : weightedScalarLevelLength (complexPlaneCoordinates '' E)
      (u ∘ complexPlaneCoordinates.symm) (q ∘ complexPlaneCoordinates.symm) =
      sobolevLevelIntegral E u q :=
    funext (complex_weighted_level_eq_physical E u q)
  rw [hlevels] at hm he
  exact ⟨hm,he.trans (complex_weighted_energy_eq_physical E u q)⟩

end CircleDomainRigidity

end

end OAI
