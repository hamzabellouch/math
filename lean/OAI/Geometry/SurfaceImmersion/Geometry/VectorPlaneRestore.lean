import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedCoordinateChange

namespace OAI

/-! Restore coordinate-plane vector fields to a smooth global displacement,
with a fixed-atlas weighted estimate and no derivative loss. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def vectorPlaneRestore (f : A.centers → SmallModes.Base → V) : M → V :=
  ∑ i : A.centers, restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry)

lemma vectorPlaneRestore_smooth (f : A.centers → SmallModes.Base → V)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) : ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.vectorPlaneRestore f) := by
  have hh : ContMDiff planeModel 𝓘(ℝ, V) ∞
      (fun x => ∑ i : A.centers, restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry) x) :=
    ContMDiff.sum (fun i _ => restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      ((hf i).comp planeCoordinateIsometry.contDiff))
  convert hh using 1
  funext x
  simp only [vectorPlaneRestore, Finset.sum_apply]

variable [CompactSpace M]

theorem vectorPlaneRestore_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (f : A.centers → SmallModes.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.WeightedBound s m (D*C) (A.vectorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := V) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  exact hd (fun i => f i ∘ planeCoordinateIsometry) s C hs hs1 hC
    (fun i => (hf i).comp planeCoordinateIsometry.contDiff)
    (fun i => weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
