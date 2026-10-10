import OAI.Geometry.SurfaceImmersion.Correction.RestoredLinearizedMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricExpansion

namespace OAI

/-! Transport the actual local linear residuals to the global metric tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance atlasLinearFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasLinearFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasLinearDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasLinearDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasLinearSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasLinearSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma linearMetricTensor_finite_sum {ι : Type*} [Fintype ι]
    (F : M → Space) (f : ι → M → Space) (hf : ∀ i, ContMDiff planeModel spaceModel ∞ (f i)) :
    linearMetricTensor F (∑ i, f i) = fun p => ∑ i, linearMetricTensor F (f i) p := by
  funext p
  ext v w
  simpa only [sum_apply,linearMetricTensor_apply] using
    linearMetricForm_finite_sum F f (fun i => ((hf i) p).mdifferentiableAt (by simp)) v w

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem vectorPlaneRestore_linearized {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (f : A.centers → SmallModes.Base → Space) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realLinearizedTensor
        (spaceCoordinates ∘ A.vectorPlaneRead i F) (spaceCoordinates ∘ f i)) := by
  unfold vectorPlaneRestore
  rw [linearMetricTensor_finite_sum F
    (fun i : A.centers => restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry))
    (fun i => restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      ((hf i).comp planeCoordinateIsometry.contDiff))]
  funext p
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.restored_linearized_metric i hF (f i) (hf i) (hsp i)) p

theorem euclidean_vectorPlaneRestore_linearized {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (f : A.centers → SmallModes.Base → RealModes.RVec 4) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realLinearizedTensor
        (spaceCoordinates ∘ A.vectorPlaneRead i F) (f i)) := by
  rw [A.euclidean_vectorPlaneRestore]
  have hh := A.vectorPlaneRestore_linearized hF (fun i => spaceCoordinates.symm ∘ f i)
    (fun i => spaceCoordinates.symm.contDiff.comp (hf i))
    (fun i => (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) (f i)).trans (hsp i))
  have he (i : A.centers) : spaceCoordinates ∘ (spaceCoordinates.symm ∘ f i) = f i := by
    funext x
    simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  simpa only [he] using hh

theorem global_linearized_residual_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ (f : A.centers → SmallModes.Base → RealModes.RVec 4),
      (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ (T : A.centers → SmallModes.Base → Tensor), (∀ i, ContDiff ℝ ∞ (T i)) →
      ∀ s C : ℝ, 0 < s → s ≤ 1 → 0 ≤ C →
      (∀ i, WeightedEstimates.WeightedBound univ s m C
        (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (f i) + T i)) →
      A.TensorWeightedBound s m (D*C)
        (linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f) + A.tensorPlaneRestore T) := by
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  refine ⟨D,hD,?_⟩
  intro F hF f hf hsp T hT s C hs hs1 hC hb
  rw [A.euclidean_vectorPlaneRestore_linearized hF f hf hsp,← A.tensorPlaneRestore_add]
  apply hd _ s C hs hs1 hC _ hb
  intro i
  apply ContDiff.add _ (hT i)
  exact contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).contDiffOn (hf i).contDiffOn)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
