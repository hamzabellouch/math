import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveNormalCoordinates
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential

namespace OAI

/-! Transfer the primitive's normal bound to the actual local phase data
used by the manifold correction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetVelocityCoordinates RealModes SurfaceJetCoordinates
open SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorChartRead_from_plane (i : A.centers) (F : M → Space) :
    (fun q => JetVelocityCoordinates.toEuclidean
      ((spaceCoordinates ∘ A.vectorPlaneRead i F) (baseEquiv q))) = A.vectorChartRead i F := by
  funext q
  change spaceCoordinates.symm (spaceCoordinates
    (A.vectorChartRead i F (planeCoordinateIsometry.symm (baseEquiv q)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [show baseEquiv q = planeCoordinateIsometry q from rfl,
    LinearIsometryEquiv.symm_apply_apply]

theorem phase_of_primitive_normal (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : JetPolynomial.Base) {c : ℝ} (hc : 0 < c)
    (hD :
      let H := primitiveNormalTriple (A.vectorChartRead i F) p
      NormalFrame.gramDet (H 0) (H 1) ≠ 0)
    (hN :
      let H := primitiveNormalTriple (A.vectorChartRead i F) p
      c < ‖realNormalPart (H 0) (H 1) (H 2)‖) :
    Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) (baseEquiv p)) ∧
      PhaseGeometry.Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (baseEquiv p))
        SmallModes.dx ∧
      c < ‖realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F)
        SmallModes.dy SmallModes.dy (baseEquiv p)‖ := by
  have hFs := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)
  have hn : realNormalPart (primitiveNormalTriple (A.vectorChartRead i F) p 0)
      (primitiveNormalTriple (A.vectorChartRead i F) p 1)
      (primitiveNormalTriple (A.vectorChartRead i F) p 2) ≠ 0 := norm_pos_iff.mp (hc.trans hN)
  have hg := good_phase_of_primitive_normal hFs p
    (by rw [A.vectorChartRead_from_plane]; exact hD)
    (by rw [A.vectorChartRead_from_plane]; exact hn)
  refine ⟨hg.1,hg.2,?_⟩
  have he := primitiveNormalTriple_chart hFs p
  rw [A.vectorChartRead_from_plane] at he
  dsimp only at hN
  rw [he] at hN
  exact hN

theorem secondTensor_margin_of_primitive_normal (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : JetPolynomial.Base) {c : ℝ} (hc : 0 < c)
    (hD :
      let H := primitiveNormalTriple (A.vectorChartRead i F) p
      NormalFrame.gramDet (H 0) (H 1) ≠ 0)
    (hN :
      let H := primitiveNormalTriple (A.vectorChartRead i F) p
      c < ‖realNormalPart (H 0) (H 1) (H 2)‖) :
    c < ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (baseEquiv p)‖ := by
  have h := (A.phase_of_primitive_normal i hF p hc hD hN).2.2
  exact h.trans_le (norm_le_pi_norm
    (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (baseEquiv p)) (2 : Fin 3))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
