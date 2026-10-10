import OAI.Geometry.SurfaceImmersion.Atlas.PhaseGaussBound
import OAI.Geometry.SurfaceImmersion.Correction.SmoothMetricGauss
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! The actual prescribed curvature has a globally smooth representative
on the compact phase region. Its choice and bound precede the loop. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_gauss_representative (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    (g : SmoothMetric M) {C : Set SmallModes.Base} (hC : IsCompact C)
    (hactive : ∀ x ∈ C, A.chartWeight i (T (baseEquiv.symm x)) ≠ 0)
    (hdet : ∀ x ∈ C, A.phaseMetricRead i T g x 0 * A.phaseMetricRead i T g x 2 -
      (A.phaseMetricRead i T g x 1)^2 ≠ 0) :
    ∃ V : Set SmallModes.Base, IsOpen V ∧ C ⊆ V ∧
    ∃ k : SmallModes.Base → ℝ, ContDiff ℝ ∞ k ∧
      (∀ x ∈ V, k x = coordinateGauss (fun y => A.phaseMetricRead i T g y 0)
        (fun y => A.phaseMetricRead i T g y 1) (fun y => A.phaseMetricRead i T g y 2) x) ∧
    ∃ B : ℝ, 1 ≤ B ∧ (∀ x ∈ C, |k x| ≤ B) ∧
      ∀ F : M → Space, IsSmoothIsometricImmersion M g F → ∀ x ∈ C,
        coordinateGauss (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dx)
          (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dy)
          (realMetric (A.phaseRealChartMap i T F) SmallModes.dy SmallModes.dy) x = k x := by
  let D := fun x => A.phaseMetricRead i T g x 0 * A.phaseMetricRead i T g x 2 -
    (A.phaseMetricRead i T g x 1)^2
  let U : Set SmallModes.Base := {x | D x ≠ 0}
  have hm := A.phaseMetricRead_smooth i hT g
  have hd : Continuous D := ((contDiff_pi.mp hm 0).mul (contDiff_pi.mp hm 2) |>.sub
    ((contDiff_pi.mp hm 1).pow 2)).continuous
  have hU : IsOpen U := isOpen_ne.preimage hd
  have hCU : C ⊆ U := hdet
  have hkg := coordinateGauss_smoothOn (contDiff_pi.mp hm 0) (contDiff_pi.mp hm 1)
    (contDiff_pi.mp hm 2) (show ∀ x ∈ U, D x ≠ 0 from fun _ hx => hx)
  obtain ⟨V,hV,hCV,_,k,hk,heq⟩ := CollarVelocity.compact_smooth_extension hC hU hCU hkg
  obtain ⟨B,hB⟩ := (hC.image hk.continuous.abs).bddAbove
  refine ⟨V,hV,hCV,k,hk,heq,max 1 B,le_max_left _ _,?_,?_⟩
  · intro x hx
    exact (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  · intro F hF x hx
    rw [A.phaseGauss_isometry i hT hF (hactive x hx)]
    exact (heq (hCV hx)).symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
