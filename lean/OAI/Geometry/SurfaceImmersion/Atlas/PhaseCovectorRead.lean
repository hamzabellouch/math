import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoefficientCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCoordinateCovector

namespace OAI

/-! The actual covector in a tangent frame is the derivative of the
scalar phase in that chart. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma covectorFrame_mfderiv (phi : M → ℝ) (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi)
    (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source) :
    B.covectorFrame i p (mfderiv planeModel 𝓘(ℝ) phi p) =
      (fderiv ℝ (phi ∘ (chart (i : M)).symm) (chart (i : M) p)).comp
        (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap := by
  let f := phi ∘ (chart (i : M)).symm
  have hf : ContDiffOn ℝ ∞ f (chart (i : M)).target :=
    (hphi.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  have hx := (chart (i : M)).map_source hp
  have hfa := hf.contDiffAt ((chart (i : M)).open_target.mem_nhds hx)
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have he : phi =ᶠ[𝓝 p] (f ∘ chart (i : M)) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hp] with q hq
    exact congrArg phi ((chart (i : M)).left_inv hq).symm
  have hd := he.mfderiv_eq (I := planeModel) (I' := 𝓘(ℝ))
  erw [mfderiv_comp p (hfa.contMDiffAt.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv,B.jetChart_tangentCoordinates i hp] at hd
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,chart_source] using hp
  apply ContinuousLinearMap.ext
  intro v
  change (mfderiv planeModel 𝓘(ℝ) phi p)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v) = _
  rw [hd]
  change fderiv ℝ f (chart (i : M) p)
      ((EuclideanSpace.equiv (Fin 2) ℝ)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v))) = _
  rw [(trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt_symmL ht]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
