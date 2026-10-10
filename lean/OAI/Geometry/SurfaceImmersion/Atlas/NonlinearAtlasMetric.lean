import OAI.Geometry.SurfaceImmersion.Geometry.SupportedLocalMetricDefect
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedPhaseMetric
import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasAnsatz
import OAI.Geometry.SurfaceImmersion.Geometry.LocalSingleTensorRestoreBound
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPrimitivePolynomial

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance nonlinearMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance nonlinearMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance nonlinearMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance nonlinearMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance nonlinearMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nonlinearMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseAtlasRemainder (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression) (B : JetPolynomial.Base → PhaseMean.Tensor) :
    JetPolynomial.Base → PhaseMean.Tensor := fun y =>
  RealModes.realMetricTensor
    (spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z ∘ planeCoordinateIsometry.symm)
    (planeCoordinateIsometry y) -
  coordinateMetricMap P z (A.jetChartMap i F ∘ e.symm) (planeCoordinateIsometry y) - B y

lemma phaseAtlasAnsatz_defect (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKO : K ⊆ O)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (γ : ∀ x : M, CovariantTwoTensor x) (B : JetPolynomial.Base → PhaseMean.Tensor) :
    inducedTensor (A.phaseAtlasAnsatz i F e χ U ℓ L z) -
        (γ + A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (localizedTensorPullback e χ B y))) =
      (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
        (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z F - γ) +
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (localizedTensorPullback e χ (A.phaseAtlasRemainder i F e U ℓ L z P B) y)) := by
  let f := A.phaseAtlasLocalIncrement i F e χ U ℓ L z
  have hf := A.phaseAtlasLocalIncrement_smooth i hF e he hi hχ U hK.isClosed hKO hzero ℓ L z
  have hs := (A.phaseAtlasLocalIncrement_support i F e hi hχs U hK hzero ℓ L z).trans hKA
  have hd := A.supported_local_metric_defect i hF f hf hs
    (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm)) z γ
    (fun y => localizedTensorPullback e χ B (planeCoordinateIsometry.symm y))
  simp only [LinearIsometryEquiv.symm_apply_apply] at hd
  change inducedTensor (F+restore (i : M) (A.outer i) f) - _ = _
  rw [hd]
  congr 1
  congr 1
  funext y
  apply congrArg fiberFromThree
  let V := spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z
  let H := A.jetChartMap i F
  have hH : ContDiff ℝ ∞ H := A.jetChartMap_smooth i hF
  have hV : ContDiff ℝ ∞ V := spaceCoordinates.contDiff.comp
    (finiteAnsatz_smooth_global ((A.vectorChartRead_smooth i hF).comp hi) U hK.isClosed hKO
      (fun j x _ hx => hzero j x hx) ℓ L z)
  have hsupport : tsupport (V-H ∘ e.symm) ⊆ K := by
    have hz := finiteAnsatz_tsupport_sub (A.vectorChartRead i F ∘ e.symm) U hK.isClosed hzero ℓ L z
    have hmaps : V-H ∘ e.symm = spaceCoordinates ∘
        (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - A.vectorChartRead i F ∘ e.symm) := by
      funext x
      exact (map_sub spaceCoordinates _ _).symm
    rw [hmaps]
    exact (tsupport_comp_subset (map_zero spaceCoordinates) _).trans hz
  have hv := supported_phase_metric_defect P e he hi hχs hK hone hH hV hsupport B z y
  have hW : H + supportedChartPullback e χ (V-H ∘ e.symm) =
      spaceCoordinates ∘ (A.vectorChartRead i F + f) := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply,Function.comp_apply,supportedChartPullback,
      V,H,jetChartMap,f,phaseAtlasLocalIncrement,map_add,map_sub,map_smul]
  rw [hW] at hv
  dsimp only [V,H] at hv
  dsimp only [localizedTensorPullback,phaseAtlasRemainder] at hv ⊢
  simpa only [coordinateMetricMap,Pi.add_apply,sub_add_eq_sub_sub,
    Function.comp_assoc] using hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
