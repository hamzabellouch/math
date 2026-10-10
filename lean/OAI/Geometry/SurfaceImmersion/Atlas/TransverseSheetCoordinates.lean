import OAI.Geometry.SurfaceImmersion.Whitney.AdaptedDoubleSheetModels
import OAI.Geometry.SurfaceImmersion.Atlas.RegularThreeChart
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingPlanes

namespace OAI

/-! Simultaneous smooth coordinate planes for an actual transverse
regular double point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure TransverseSheetCoordinates (f : M → ProjectionTarget 3) (x y : M) where
  left : OpenPartialHomeomorph M Base
  right : OpenPartialHomeomorph M Base
  target : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3)
  left_mem : x ∈ left.source
  right_mem : y ∈ right.source
  left_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ left left.source
  right_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ right right.source
  left_inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ left.symm left.target
  right_inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ right.symm right.target
  target_smooth : ContDiff ℝ ∞ target
  target_inverse_smooth : ContDiffOn ℝ ∞ target.symm target.target
  left_formula : ∀ q ∈ left.source, leftCrossingPlane (left q) ∈ target.source ∧
    f q = target (leftCrossingPlane (left q))
  right_formula : ∀ q ∈ right.source, rightCrossingPlane (right q) ∈ target.source ∧
    f q = target (rightCrossingPlane (right q))

theorem LocalDoubleSheetModel.simultaneous_coordinates {f : M → ProjectionTarget 3}
    {x y : M} {t : ℝ} (m : LocalDoubleSheetModel f x y t) :
    Nonempty (TransverseSheetCoordinates f x y) := by
  let T := crossingCoordinateMap m.F m.G
  have hT : ContDiff ℝ ∞ T := crossingCoordinateMap_smooth m.F_smooth m.G_smooth
  obtain ⟨e,he0,he,hei⟩ := regular_three_chart hT (0,t) m.crossing_regular
  obtain ⟨V,hVeq,hV,hxV⟩ := eventually_nhds_iff.mp m.left_model
  obtain ⟨W,hWeq,hW,hyW⟩ := eventually_nhds_iff.mp m.right_model
  obtain ⟨J,hJeq,hJ,htJ⟩ := eventually_nhds_iff.mp m.common_axis
  let L := V ∩ (m.left.source ∩ m.left ⁻¹'
    (leftCrossingPlane ⁻¹' e.source ∩ (fun u : Base => u 1) ⁻¹' J))
  let R := W ∩ (m.right.source ∩ m.right ⁻¹' (rightCrossingPlane ⁻¹' e.source))
  have hL : IsOpen L := hV.inter (m.left.isOpen_inter_preimage
    ((e.open_source.preimage leftCrossingPlane_smooth.continuous).inter
      (hJ.preimage (continuous_apply 1))))
  have hR : IsOpen R := hW.inter (m.right.isOpen_inter_preimage
    (e.open_source.preimage rightCrossingPlane_smooth.continuous))
  have hxL : x ∈ L := by
    refine ⟨hxV,m.left_mem,?_,?_⟩
    · change leftCrossingPlane (m.left x) ∈ e.source
      rw [m.left_center,leftCrossingPlane_axis]
      exact he0
    · change (m.left x) 1 ∈ J
      rw [m.left_center]
      exact htJ
  have hyR : y ∈ R := by
    refine ⟨hyW,m.right_mem,?_⟩
    change rightCrossingPlane (m.right y) ∈ e.source
    rw [m.right_center,rightCrossingPlane_axis]
    exact he0
  let a := m.left.restrOpen L hL
  let b := m.right.restrOpen R hR
  refine ⟨⟨a,b,e,⟨m.left_mem,hxL⟩,⟨m.right_mem,hyR⟩,
    m.left_smooth.mono (fun _ h => h.1),m.right_smooth.mono (fun _ h => h.1),
    m.left_inverse_smooth.mono (fun _ h => h.1),m.right_inverse_smooth.mono (fun _ h => h.1),
    by simpa only [he] using hT,hei,?_,?_⟩⟩
  · intro q hq
    have hmem : leftCrossingPlane (m.left q) ∈ e.source := hq.2.2.2.1
    have haxis : m.F ![0,(m.left q) 1] = m.G ![0,(m.left q) 1] := hJeq _ hq.2.2.2.2
    refine ⟨hmem,?_⟩
    change f q = e (leftCrossingPlane (m.left q))
    rw [he]
    change f q = crossingCoordinateMap m.F m.G (leftCrossingPlane (m.left q))
    rw [crossingCoordinateMap_leftPlane _ haxis]
    exact hVeq q hq.2.1
  · intro q hq
    have hmem : rightCrossingPlane (m.right q) ∈ e.source := hq.2.2.2
    refine ⟨hmem,?_⟩
    change f q = e (rightCrossingPlane (m.right q))
    rw [he]
    change f q = crossingCoordinateMap m.F m.G (rightCrossingPlane (m.right q))
    rw [crossingCoordinateMap_rightPlane]
    exact hWeq q hq.2.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
