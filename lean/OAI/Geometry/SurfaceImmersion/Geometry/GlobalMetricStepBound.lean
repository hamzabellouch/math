import OAI.Geometry.SurfaceImmersion.Geometry.GlobalMetricStep
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAtlasQuadraticResidual

namespace OAI

/-! Global weighted estimate for the concrete unsmoothed normalized-defect update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance stepBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance stepBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance stepBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance stepBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance stepBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance stepBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorWeightedBound_sub {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T-S) := by
  intro i
  have he : A.bundleLocalize A.tensorTriv i (T-S) =
      A.bundleLocalize A.tensorTriv i T - A.bundleLocalize A.tensorTriv i S := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).target <;>
      simp [bundleLocalize,localize,bundleComponent,hx,smul_sub]
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T-S))
  rw [he]
  exact (hbT i).sub uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

include A in
lemma normalizedTensorDefect_smooth {target : ∀ p : M, CovariantTwoTensor p}
    (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    (δ : ℝ) {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (normalizedTensorDefect target δ F p)) :=
  (ht.sub_section (A.inducedTensor_smooth hF)).const_smul_section

include A in
lemma realizedTensorError_smooth {target Hs : ∀ p : M, CovariantTwoTensor p}
    (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    (hs : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (Hs p)))
    (δ δ' : ℝ) {G U : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (realizedTensorError target Hs δ δ' G U p)) :=
  ((A.inducedTensor_smooth (hG.add hU)).sub_section (A.inducedTensor_smooth hG)).sub_section
    (hs.const_smul_section.sub_section ht.const_smul_section)

theorem global_normalized_metric_step_bound {target Hs : ∀ p : M, CovariantTwoTensor p}
    (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    (hs : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (Hs p)))
    {δ δ' τ BH BE BC : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0) (hτ : 0 ≤ τ) (m : ℕ)
    {F G U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U)
    (hbH : A.TensorWeightedBound τ m BH (normalizedTensorDefect target δ F-Hs))
    (hbE : A.TensorWeightedBound τ m BE (realizedTensorError target Hs δ δ' G U))
    (hbC : A.TensorWeightedBound τ m BC (linearMetricTensor (F-G) U)) :
    A.TensorWeightedBound τ m ((δ'^2)⁻¹*(δ^2*BH+BE+BC))
      (normalizedTensorDefect target δ' (F+U)-target) := by
  have hHs := (A.normalizedTensorDefect_smooth ht δ hF).sub_section hs
  have hEs := A.realizedTensorError_smooth ht hs δ δ' hG hU
  have hCs := A.linearMetricTensor_smooth (hF.sub hG) hU
  have h₁ := A.tensorWeightedBound_const_smul hHs hbH (δ^2)
  rw [abs_of_nonneg (sq_nonneg δ)] at h₁
  have h₂ := A.tensorWeightedBound_sub hHs.const_smul_section hEs hτ h₁ hbE
  have h₃ := A.tensorWeightedBound_sub (hHs.const_smul_section.sub_section hEs) hCs hτ h₂ hbC
  have h₄ := A.tensorWeightedBound_const_smul
    ((hHs.const_smul_section.sub_section hEs).sub_section hCs) h₃ ((δ'^2)⁻¹)
  rw [abs_inv,abs_of_nonneg (sq_nonneg δ')] at h₄
  have heq : normalizedTensorDefect target δ' (F+U)-target = (δ'^2)⁻¹ •
      (δ^2 • (normalizedTensorDefect target δ F-Hs) - realizedTensorError target Hs δ δ' G U -
        linearMetricTensor (F-G) U) := by
    rw [← global_normalized_defect_identity target Hs hδ hδ' hF hG hU,
      smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hδ'),one_smul]
  rw [heq]
  exact h₄

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
