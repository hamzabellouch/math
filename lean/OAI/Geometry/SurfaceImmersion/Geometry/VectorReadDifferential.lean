import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasDifferential
import OAI.Geometry.SurfaceImmersion.Geometry.ManifoldMetricCalculus

namespace OAI

/-! Coordinate representatives recover the actual manifold differential
on each original phase support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_fderiv (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    fderiv ℝ (A.vectorChartRead i F) x = fderiv ℝ (F ∘ (chart (i : M)).symm) x := by
  ext v
  have hh := congrArg (fun T => T (fun _ : Fin 1 => v)) (A.vectorChartRead_jets i hF 1 hx)
  simpa only [iteratedFDeriv_one_apply] using hh

lemma vectorChartRead_differential (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    surfaceDifferential F p = (fderiv ℝ (A.vectorChartRead i F) (chart (i : M) p)).comp
      (surfaceDifferential (chart (i : M)) p) := by
  have hs := A.weight_support i hp
  have hx := (chart (i : M)).map_source hs
  have hc := ((chart_smooth (i : M)) p hs).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hs)
  have hi : DifferentiableAt ℝ (F ∘ (chart (i : M)).symm) (chart (i : M) p) :=
    (((hF.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn).contDiffAt
      ((chart (i : M)).open_target.mem_nhds hx)).differentiableAt (by simp)
  rw [A.vectorChartRead_fderiv i hF ⟨p,hp,rfl⟩]
  have he : F =ᶠ[𝓝 p] (F ∘ (chart (i : M)).symm) ∘ chart (i : M) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hs] with q hq
    simp only [Function.comp_apply,(chart (i : M)).left_inv hq]
  unfold surfaceDifferential
  rw [he.mfderiv_eq]
  change surfaceDifferential ((F ∘ (chart (i : M)).symm) ∘ chart (i : M)) p = _
  have hm := mfderiv_comp p hi.mdifferentiableAt (hc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hm
  exact hm

lemma vectorPlaneRead_chain (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) (x : JetPolynomial.Base) :
    (fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry x)).comp
      planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap =
        fderiv ℝ (A.vectorChartRead i F) x := by
  have hh := (((A.vectorChartRead_smooth i hF).differentiable (by simp)
    (planeCoordinateIsometry.symm (planeCoordinateIsometry x))).hasFDerivAt.comp (planeCoordinateIsometry x)
      planeCoordinateIsometry.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  simp only [LinearIsometryEquiv.symm_apply_apply] at hh
  change fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry x) = _ at hh
  rw [hh]
  ext v
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply]

lemma vectorPlaneRead_differential (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    surfaceDifferential F p =
      (fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p))).comp
        (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (surfaceDifferential (chart (i : M)) p)) := by
  rw [← ContinuousLinearMap.comp_assoc,A.vectorPlaneRead_chain i hF]
  exact A.vectorChartRead_differential i hF hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
