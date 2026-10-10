import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasMetric
import OAI.Geometry.SurfaceImmersion.Geometry.SingleTensorRestoreBound
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveErrorBound
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
local instance nonlinearErrorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance nonlinearErrorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance nonlinearErrorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance nonlinearErrorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance nonlinearErrorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nonlinearErrorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseAtlasRemainder_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {B : JetPolynomial.Base → PhaseMean.Tensor} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (A.phaseAtlasRemainder i F e U ℓ L z P B) := by
  have hbase := (A.jetChartMap_smooth i hF).comp hi
  have hV := spaceCoordinates.contDiff.comp
    (finiteAnsatz_smooth_global ((A.vectorChartRead_smooth i hF).comp hi) U hK hKO
      (fun j x _ hx => hzero j x hx) ℓ L z)
  have hm (f : JetPolynomial.Base → JetPolynomial.Space) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (fun y => RealModes.realMetricTensor (f ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry y)) :=
    (contDiffOn_univ.mp (RealModes.contDiffOn_realMetricTensor isOpen_univ
      (hf.comp planeCoordinateIsometry.symm.contDiff).contDiffOn)).comp planeCoordinateIsometry.contDiff
  have hh := (((hm _ hV).sub (hm _ hbase)).sub
    ((coordinatePolynomialValue_smooth hP hbase z).comp planeCoordinateIsometry.contDiff)).sub hB
  convert hh using 1
  funext y
  simp only [phaseAtlasRemainder,coordinateMetricMap,Pi.add_apply,Function.comp_apply,Function.comp_assoc]
  rw [sub_add_eq_sub_sub]

/-- A local phase remainder and the actual solved mean control the global metric error. -/
theorem phaseAtlasAnsatz_error_bound (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    {W : Set JetPolynomial.Base} (hW : IsOpen W) (hTW : MapsTo e e.source W) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
    ∀ (O : TopologicalSpace.Opens JetPolynomial.Base) (U : ℕ → Family O Space)
      (K : Set JetPolynomial.Base), IsCompact K → K ⊆ O →
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
      (∀ j x, x ∉ K → (U j).val x = 0) →
      (∀ x ∈ e.symm '' K, χ x = 1) →
    ∀ (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) (n : ℕ)
      (P : Fin 3 → Fin n → Expression), (∀ k r, (P k r).SmoothCoeffs univ) →
    ∀ (γ : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
    ∀ (B : JetPolynomial.Base → PhaseMean.Tensor), ContDiff ℝ ∞ B →
    ∀ (s C E : ℝ), 0 < s → s ≤ 1 → 0 ≤ E →
      A.TensorWeightedBound s m C (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
        (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z F-γ) →
      WeightedEstimates.WeightedBound W s m E (A.phaseAtlasRemainder i F e U ℓ L z P B) →
      A.TensorWeightedBound s m (C+D*E)
        (inducedTensor (A.phaseAtlasAnsatz i F e χ U ℓ L z)-
          (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (localizedTensorPullback e χ B y)))) := by
  obtain ⟨Dt,hDt,ht⟩ := localized_tensor_pullback_bound he hχ hχc e.open_source hW hχs hTW m
  obtain ⟨Dr,hDr,hr⟩ := A.single_tensor_restore_bound i m
  refine ⟨Dr*Dt,mul_nonneg hDr hDt,?_⟩
  intro F hF O U K hK hKO hKA hzero hone ℓ L z n P hP γ hγ B hB s C E hs hs1 hE hmean hrem
  have hR := A.phaseAtlasRemainder_smooth i hF e hi U hK.isClosed hKO hzero ℓ L z hP hB
  have hpull := localizedTensorPullback_smooth he hχ hR
  have hb := ht _ s E hs hs1 hE hR hrem
  have htensor := weightedBound_comp_isometry_on planeCoordinateIsometry.symm isOpen_univ hpull hb
  have hrb := hr (localizedTensorPullback e χ (A.phaseAtlasRemainder i F e U ℓ L z P B) ∘
      planeCoordinateIsometry.symm) s (Dt*E) hs hs1 (mul_nonneg hDt hE)
    (hpull.comp planeCoordinateIsometry.symm.contDiff) (by simpa only [preimage_univ] using htensor)
  simp only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] at hrb
  have hRs := A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
    (fiberFromThree.contDiff.comp hpull)
  have hPm := cutoffTensorPolynomial_smooth hχ (tensorPolynomialCoordinatePullback_smooth hP he hi)
  have hms := (A.atlasPolynomialMetric_smooth (A.primitiveAtlasPolynomial_smooth i hPm) hF z).sub_section hγ
  have hadd := A.tensorWeightedBound_add hms hRs hs.le hmean hrb
  rw [A.phaseAtlasAnsatz_defect i hF e he hi hχ hχs U hK hKO hKA hzero hone ℓ L z P γ B]
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply,mul_assoc] using hadd

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
