import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveErrorBound
import OAI.Geometry.SurfaceImmersion.Geometry.LocalSingleTensorRestoreBound

namespace OAI

/-! A local finite periodic remainder and a global solved mean error control
the metric of the actual globally restored primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
local instance primitiveLocalBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveLocalBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance primitiveLocalBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveLocalBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitiveLocalBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveLocalBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- No error is lost in globalization; the only new constant is the fixed
single-patch tensor restoration norm. -/
theorem periodicAtlasAnsatz_error_bound_on_outer (i : A.centers)
    {V : Set JetPolynomial.Base} (hV : IsOpen V)
    (houter : (chart (i : M)) '' tsupport (A.outer i) ⊆ V) (m : ℕ) :
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
      WeightedEstimates.WeightedBound (planeCoordinateIsometry.symm ⁻¹' V) s m E (A.periodicAtlasRemainder i F U ℓ L z P H) →
      A.TensorWeightedBound s m (C+D*E)
        (inducedTensor (A.periodicAtlasAnsatz i F U ℓ L z)-
          (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (H (planeCoordinateIsometry y))))) := by
  obtain ⟨D,hD,hd⟩ := A.single_tensor_restore_bound_on_outer i hV houter m
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
