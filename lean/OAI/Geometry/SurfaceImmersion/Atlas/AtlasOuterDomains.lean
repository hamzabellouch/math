import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Bounded open coordinate domains containing every outer cutoff support. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_outer_domains :
    ∃ (U : A.centers → Set JetPolynomial.Base) (K : A.centers → Compacts JetPolynomial.Base),
      (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ K i) ∧
      (∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i) ∧
      (∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i) := by
  classical
  have hc (i : A.centers) : IsCompact ((chart (i : M)) '' tsupport (A.outer i)) :=
    (isClosed_tsupport (A.outer i)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (A.outer_support i))
  choose U hU hKU hUc _ using fun i => CollarVelocity.compact_open_thickening
    (hc i) isOpen_univ (subset_univ _)
  refine ⟨U,fun i => ⟨closure (U i),hUc i⟩,hU,fun _ => subset_closure,?_,hKU⟩
  intro i x hx
  obtain ⟨p,hp,rfl⟩ := hx
  apply hKU i
  refine ⟨p,subset_tsupport (A.outer i) ?_,rfl⟩
  change A.outer i p ≠ 0
  rw [A.outer_one i p hp]
  exact one_ne_zero

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
