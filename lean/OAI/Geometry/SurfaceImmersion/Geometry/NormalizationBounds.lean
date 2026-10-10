import OAI.Geometry.SurfaceImmersion.Correction.NormalizedJetCorrection
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Normalization preserves a uniform C2 budget when the image stays in a
fixed compact set separated from the origin. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets
open WeightedEstimates

theorem compact_normalization_C2_bound {K : Set Space} (hK : IsCompact K)
    (hK0 : ∀ x ∈ K, x ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (U : Set Plane), UniqueDiffOn ℝ U →
      ∀ (F : Plane → Space) (C : ℝ), 1 ≤ C → ContDiffOn ℝ ∞ F U →
        MapsTo F U K → WeightedBound U 1 2 C F →
        WeightedBound U 1 2 (2*D*C^2) (radialNormalize ∘ F) := by
  let V : Set Space := {x | x ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun continuous_id continuous_const
  have hn : ContDiffOn ℝ ∞ radialNormalize V :=
    fun x hx => (radialNormalize_smoothAt hx).contDiffWithinAt
  obtain ⟨D,hD,hb⟩ := compact_coefficient_bound hV.uniqueDiffOn hK hK0 hn 2
  refine ⟨D,hD,?_⟩
  intro U hU F C hC hF hFK hFC
  have hc := hFC.comp hU hV.uniqueDiffOn zero_lt_one hC (zero_le_one.trans hD)
    hF hn (fun x hx => hK0 _ (hFK hx)) (fun j hj x hx => hb j hj (F x) (hFK hx))
  simpa using hc

end ClosedSurfaceR4.SphericalJets

end

end OAI
