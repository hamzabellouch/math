import OAI.Geometry.SurfaceImmersion.Geometry.LocalSecondFormNaturality
import OAI.Geometry.SurfaceImmersion.Atlas.CenteredAtlasDifferentials

namespace OAI

/-! The pure radial form is independent of the selected surface chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma radial_form_coordinate_transfer {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (q p a : M) (haq : a ∈ (coordinateChart q).source)
    (hap : a ∈ (coordinateChart p).source)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateChart q a))
      (coordDeriv dy (coordinateMap F q) (coordinateChart q a)) ≠ 0)
    (n : RVec 4) (r : ℝ)
    (hB : ∀ v w, realSecondForm (coordinateMap F q) v w (coordinateChart q a) =
      (r⁻¹*(coordDeriv v (coordinateMap F q) (coordinateChart q a) ⬝ᵥ
        coordDeriv w (coordinateMap F q) (coordinateChart q a))) • n)
    (v w : Base) :
    realSecondForm (coordinateMap F p) v w (coordinateChart p a) =
      (r⁻¹*(coordDeriv v (coordinateMap F p) (coordinateChart p a) ⬝ᵥ
        coordDeriv w (coordinateMap F p) (coordinateChart p a))) • n := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have he := coordinateTransition_apply_chart q p hap
  have ht : coordinateTransition q p (coordinateChart p a) ∈ coordinateDomain q := by
    rw [he,← coordinateChart_target]
    exact (coordinateChart q).map_source haq
  have hb := pure_radial_comp_on (coordinateTransition q p).open_source
    (coordinateDomain_open q) (coordinateMap_smoothOn hF q)
    (coordinateTransition_smoothOn q p) hx ht
    (by simpa only [he] using hD) (coordinateTransition_det_ne q p hx) n r
    (by simpa only [he] using hB) v w
  have hg := coordinateMap_transition_eventuallyEq F q p hx
  rw [(realSecondForm_eventuallyEq hg v w).eq_of_nhds,
    (coordDeriv_eventuallyEq hg v).eq_of_nhds,
    (coordDeriv_eventuallyEq hg w).eq_of_nhds] at hb
  exact hb

end ClosedSurfaceR4

end

end OAI
