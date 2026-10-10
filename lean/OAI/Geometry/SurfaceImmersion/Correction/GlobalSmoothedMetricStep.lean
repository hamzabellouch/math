import OAI.Geometry.SurfaceImmersion.Geometry.GlobalMetricStepBound
import OAI.Geometry.SurfaceImmersion.Geometry.GlobalShiftedLinearMetricBound
import OAI.Geometry.SurfaceImmersion.Correction.CoupledSmoothing

namespace OAI

/-! The actual smoothed update has a defect bound linear in higher input norms. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance smoothStepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance smoothStepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem smoothed_normalized_metric_step_bound (r m : ℕ) :
    ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧
    ∀ (target : ∀ p : M, CovariantTwoTensor p),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (target p)) →
    ∀ (F U : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ContMDiff planeModel spaceModel ∞ U →
    ∀ (δ δ' τ s t B C K R : ℝ), δ ≠ 0 → δ' ≠ 0 →
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C → 0 ≤ K →
      A.InputBound t r B F (normalizedTensorDefect target δ F) →
      A.InputBound t m C F (normalizedTensorDefect target δ F) →
      A.WeightedBound τ (m+1) K U →
      A.TensorWeightedBound τ m R
        (realizedTensorError target
          (A.tensorSmooth r s (normalizedTensorDefect target δ F)) δ δ' (A.smooth r s F) U) →
      A.TensorWeightedBound τ m
        ((δ'^2)⁻¹ *
          ((δ^2 + E*K/τ) * (D*tailConstant r*(B*(s/t)^r+C*(τ/t)^r)) + R))
        (normalizedTensorDefect target δ' (F+U)-target) := by
  obtain ⟨D,hD,hd⟩ := A.coupled_smoothing_tail r m
  obtain ⟨E,hE,he⟩ := A.global_shifted_linear_metric_bound m
  refine ⟨D,E,hD,hE,?_⟩
  intro target ht F U hF hU δ δ' τ s t B C K R hδ hδ' hτ hτs hst ht1 hB hC hK hb hc hu hr
  have hs : 0 < s := hτ.trans_le hτs
  have htpos : 0 < t := hs.trans_le hst
  have hτ1 : τ ≤ 1 := hτs.trans (hst.trans ht1)
  have hH := A.normalizedTensorDefect_smooth ht δ hF
  have hG := A.smooth_smooth r hs hF
  have hHs := A.tensorSmooth_smooth r hs hH
  let T := D*tailConstant r*(B*(s/t)^r+C*(τ/t)^r)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg hD (tailConstant_nonneg r)) (by positivity)
  have htail := hd F (normalizedTensorDefect target δ F) s t τ B C
    hτ hτs hst ht1 hB hC hF hH hb hc
  have hcross := he τ T K hτ hτ1 hT hK (F-A.smooth r s F) U
    (hF.sub hG) hU (A.shiftedBound_lower_prefix htail.1 hτ.le hτ1 (by omega) (by omega)) hu
  have hout := A.global_normalized_metric_step_bound ht hHs hδ hδ' hτ.le m
    hF hG hU htail.2 hr hcross
  convert hout using 1
  dsimp [T]
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
