import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights
import OAI.Geometry.SurfaceImmersion.Geometry.VectorPlaneRestore

namespace OAI

/-! A displacement supported on an atlas weight's compact support is
restored exactly in that chart; the outer cutoff introduces no jet error. -/
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma mem_weight_support_of_plane (i : A.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (h : planeCoordinateIsometry (chart (i : M) p) ∈
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) : p ∈ tsupport (A.weight i) := by
  obtain ⟨y,hy,he⟩ := h
  have hyEq : y = chart (i : M) p := planeCoordinateIsometry.injective he
  subst y
  obtain ⟨q,hq,hqp⟩ := hy
  have hqEq : q = p := (chart (i : M)).injOn (A.weight_support i hq) hp hqp
  rwa [hqEq] at hq

lemma restore_plane_on_source (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) p =
      f (planeCoordinateIsometry (chart (i : M) p)) := by
  rw [restore,indicator_of_mem hp]
  change A.outer i p • f (planeCoordinateIsometry (chart (i : M) p)) = _
  by_cases hz : f (planeCoordinateIsometry (chart (i : M) p)) = 0
  · rw [hz,smul_zero]
  · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hf (subset_tsupport f hz))),one_smul]

lemma restore_plane_in_coordinates (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {x : JetPolynomial.Base} (hx : x ∈ (chart (i : M)).target) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) ((chart (i : M)).symm x) =
      f (planeCoordinateIsometry x) := by
  rw [A.restore_plane_on_source i f hf ((chart (i : M)).map_target hx),(chart (i : M)).right_inv hx]

lemma restore_plane_coordinate_derivative (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {x : JetPolynomial.Base} (hx : x ∈ (chart (i : M)).target) :
    fderiv ℝ (fun y => restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)
      ((chart (i : M)).symm y)) x = fderiv ℝ (f ∘ planeCoordinateIsometry) x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(chart (i : M)).open_target.mem_nhds hx] with y hy
  exact A.restore_plane_in_coordinates i f hf hy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
