import OAI.Geometry.SurfaceImmersion.Atlas.GridPhaseCutoffs
import OAI.Geometry.SurfaceImmersion.Atlas.ChartReadSupport
import OAI.Geometry.Immersion.ClosedSurface.GlobalPartition
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasDifferential

namespace OAI

/-! The local cell cutoff has the exact global refined support used in
phase selection. This keeps the solver's geometry on that original support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma cellCutoff_eq_vectorPlaneRead (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    A.vectorPlaneRead i (refinedCutoff (i : M) (A.weight i) a h k) =
      fun y => A.planeWeight i y * normalizedCutoff a h k y := by
  funext y
  change (chart (i : M)).target.indicator (fun x =>
      (A.outer i ((chart (i : M)).symm x))^2 *
        refinedCutoff (i : M) (A.weight i) a h k ((chart (i : M)).symm x))
      (planeCoordinateIsometry.symm y) = _
  by_cases hy : planeCoordinateIsometry.symm y ∈ (chart (i : M)).target
  · have he : chartCoordinates (i : M)
        ((chart (i : M)).symm (planeCoordinateIsometry.symm y)) = y := by
      change planeCoordinateIsometry ((chart (i : M))
        ((chart (i : M)).symm (planeCoordinateIsometry.symm y))) = y
      rw [(chart (i : M)).right_inv hy,LinearIsometryEquiv.apply_symm_apply]
    simp only [refinedCutoff,he,planeWeight,Function.comp_apply,
      chartWeight,indicator_of_mem hy]
    by_cases hw : A.weight i ((chart (i : M)).symm (planeCoordinateIsometry.symm y)) = 0
    · simp only [hw,zero_mul,mul_zero]
    · rw [A.outer_one i _ (subset_tsupport _ hw),one_pow,one_mul]
  · simp only [planeWeight,Function.comp_apply,chartWeight,
      indicator_of_notMem hy,zero_mul]

def cellChartCompact (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    TopologicalSpace.Compacts JetPolynomial.Base :=
  ⟨(chart (i : M)) '' tsupport (refinedCutoff (i : M) (A.weight i) a h k),
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono ((refinedCutoff_tsupport_outer
        (i : M) (A.weight i) a h k).trans (A.weight_support i)))⟩

lemma cellChartCompact_subset (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    (A.cellChartCompact i a h k : Set JetPolynomial.Base) ⊆ A.chartWeightCompact i :=
  Set.image_mono (refinedCutoff_tsupport_outer (i : M) (A.weight i) a h k)

lemma cellCutoff_tsupport (i : A.centers) {a : Finset Index} {h : ℝ}
    (hh : 0 < h)
    (hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion a h)
    (k : Index) :
    tsupport (supportedCellCutoff (A.supportedPlaneWeight i) hh hcover k) ⊆
      (modeSupport (A.cellChartCompact i a h k) : Set SmallModes.Base) := by
  let f := supportedCellCutoff (A.supportedPlaneWeight i) hh hcover k
  have he : (f : SmallModes.Base → ℝ) =
      A.vectorPlaneRead i (refinedCutoff (i : M) (A.weight i) a h k) := by
    rw [A.cellCutoff_eq_vectorPlaneRead]
    rfl
  intro y hy
  have hK : y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (f.tsupport_subset hy).1
  have hr := A.vectorPlaneRead_support_on_weight i
    (refinedCutoff (i : M) (A.weight i) a h k) hK (by simpa only [← he] using hy)
  obtain ⟨x,⟨p,hp,rfl⟩,rfl⟩ := hK
  refine ⟨chart (i : M) p,⟨p,?_,rfl⟩,rfl⟩
  simpa only [LinearIsometryEquiv.symm_apply_apply,
    (chart (i : M)).left_inv (A.weight_support i hp)] using hr

def exactCellCutoff (i : A.centers) {a : Finset Index} {h : ℝ}
    (hh : 0 < h)
    (hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion a h)
    (k : Index) : SupportedField (F := ℝ) (modeSupport (A.cellChartCompact i a h k)) :=
  ContDiffMapSupportedIn.of_support_subset
    (supportedCellCutoff (A.supportedPlaneWeight i) hh hcover k).contDiff
    ((subset_tsupport _).trans (A.cellCutoff_tsupport i hh hcover k))

@[simp] lemma exactCellCutoff_apply (i : A.centers) {a : Finset Index} {h : ℝ}
    (hh : 0 < h)
    (hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion a h)
    (k : Index) (x : SmallModes.Base) :
    A.exactCellCutoff i hh hcover k x = A.planeWeight i x * normalizedCutoff a h k x := rfl

lemma restore_cell_tsupport {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index)
    (f : JetPolynomial.Base → V)
    (hf : tsupport f ⊆ (A.cellChartCompact i a h k : Set JetPolynomial.Base)) :
    tsupport (restore (i : M) (A.outer i) f) ⊆
      tsupport (refinedCutoff (i : M) (A.weight i) a h k) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · have hn : f (chart (i : M) p) ≠ 0 := by
      intro hz
      apply hp
      simp only [restore,indicator_of_mem hs,hz,smul_zero]
    obtain ⟨q,hq,he⟩ := hf (subset_tsupport f hn)
    have hqs := A.weight_support i
      (refinedCutoff_tsupport_outer (i : M) (A.weight i) a h k hq)
    have hqp : q = p := (chart (i : M)).injOn hqs hs he
    simpa only [hqp] using hq
  · exfalso
    apply hp
    simp only [restore,indicator_of_notMem hs]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
