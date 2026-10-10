import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveError
import OAI.Geometry.SurfaceImmersion.Geometry.SingleTensorRestoreBound

namespace OAI

/-! A local finite periodic remainder and a global solved mean error control
the metric of the actual globally restored primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
local instance primitiveBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance primitiveBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitiveBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def periodicAtlasRemainder (i : A.centers) (F : M → Space)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression) (H : SmallModes.Base → PhaseMean.Tensor) :
    SmallModes.Base → PhaseMean.Tensor :=
  RealModes.realMetricTensor
    (spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F) U ℓ L z ∘ planeCoordinateIsometry.symm)-
    RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)-
    coordinatePolynomialValue P z (A.jetChartMap i F) 0-H

lemma periodicAtlasRemainder_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {H : SmallModes.Base → PhaseMean.Tensor} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (A.periodicAtlasRemainder i F U ℓ L z P H) := by
  have ha := finiteAnsatz_smooth_global (A.vectorChartRead_smooth i hF) U hK hKO
    (fun j x _ hx => hzero j x hx) ℓ L z
  have hmetric (f : SmallModes.Base → RealModes.RVec 4) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (RealModes.realMetricTensor f) :=
    contDiffOn_univ.mp (RealModes.contDiffOn_realMetricTensor isOpen_univ hf.contDiffOn)
  exact (((hmetric _ (spaceCoordinates.contDiff.comp (ha.comp planeCoordinateIsometry.symm.contDiff))).sub
    (hmetric _ (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)))).sub
    (coordinatePolynomialValue_smooth hP (A.jetChartMap_smooth i hF) z)).sub hH

/-- No error is lost in globalization; the only new constant is the fixed
single-patch tensor restoration norm. -/
theorem periodicAtlasAnsatz_error_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
    ∀ (O : TopologicalSpace.Opens JetPolynomial.Base) (U : ℕ → Family O Space)
      (K : Set JetPolynomial.Base), IsClosed K → K ⊆ O →
      K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
      (∀ j x, x ∉ K → (U j).val x = 0) →
    ∀ (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) (n : ℕ)
      (P : Fin 3 → Fin n → Expression), (∀ k r, (P k r).SmoothCoeffs univ) →
    ∀ (γ : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
    ∀ (H : SmallModes.Base → PhaseMean.Tensor), ContDiff ℝ ∞ H →
    ∀ (s C E : ℝ), 0 < s → s ≤ 1 → 0 ≤ E →
      A.TensorWeightedBound s m C (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i P) z F-γ) →
      WeightedEstimates.WeightedBound univ s m E (A.periodicAtlasRemainder i F U ℓ L z P H) →
      A.TensorWeightedBound s m (C+D*E)
        (inducedTensor (A.periodicAtlasAnsatz i F U ℓ L z)-
          (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (H (planeCoordinateIsometry y))))) := by
  obtain ⟨D,hD,hd⟩ := A.single_tensor_restore_bound i m
  refine ⟨D,hD,?_⟩
  intro F hF O U K hK hKO hKA hzero ℓ L z n P hP γ hγ H hH s C E hs hs1 hE hmean hrem
  have hR := A.periodicAtlasRemainder_smooth i hF U hK hKO hzero ℓ L z hP hH
  have hr := hd _ s E hs hs1 hE hR hrem
  have hRs := A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
    (fiberFromThree.contDiff.comp (hR.comp planeCoordinateIsometry.contDiff))
  have hm := (A.atlasPolynomialMetric_smooth (A.primitiveAtlasPolynomial_smooth i hP) hF z).sub_section hγ
  have hb := A.tensorWeightedBound_add hm hRs hs.le hmean hr
  rw [A.periodicAtlasAnsatz_defect i hF U hK hKO hKA hzero ℓ L z P γ H]
  exact hb

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
