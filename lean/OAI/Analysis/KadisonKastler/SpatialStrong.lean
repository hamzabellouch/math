import OAI.Analysis.KadisonKastler.SpatialProduct
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

/-! # Bounded strong continuity of the spatial right representation -/

namespace KadisonKastler

open UnitalTomsWinter Filter
open scoped TensorProduct Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A uniformly bounded strongly convergent family remains strongly
convergent after amplification in the right tensor leg. -/
theorem spatialRight_tendsto_strong
    {ι : Type*} {l : Filter ι} (T : ι → K →L[ℂ] K) (a : K →L[ℂ] K)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C)
    (ha : ∀ y, Tendsto (fun i => T i y) l (𝓝 (a y)))
    (z : SpatialHilbert H K) :
    Tendsto (fun i => spatialRight (H := H) (T i) z) l
      (𝓝 (spatialRight (H := H) a z)) := by
  have hequi : Equicontinuous
      (fun i : ι => (spatialRight (H := H) (T i) : SpatialHilbert H K → SpatialHilbert H K)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C * t)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0))))
    intro x y i
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    have hn : ‖spatialRight (H := H) (T i)‖ ≤ C := by
      calc
        _ ≤ ‖(1 : H →L[ℂ] H)‖ * ‖T i‖ := spatialTensorOp_norm_le _ _
        _ ≤ 1 * ‖T i‖ := mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.norm_id_le : ‖(1 : H →L[ℂ] H)‖ ≤ 1) (norm_nonneg _)
        _ ≤ C := by simpa only [one_mul] using hT i
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hequi.isClosed_setOfPred_tendsto (spatialRight (H := H) a).continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      let L : K →L[ℂ] SpatialHilbert H K :=
        UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ H K x)
      have h := L.continuous.continuousAt.tendsto.comp (ha y)
      change Tendsto (fun i => ((x ⊗ₜ[ℂ] (T i y) : H ⊗[ℂ] K) : SpatialHilbert H K))
        l (𝓝 ((x ⊗ₜ[ℂ] (a y) : H ⊗[ℂ] K) : SpatialHilbert H K)) at h
      change Tendsto (fun i => spatialTensorOp (1 : H →L[ℂ] H) (T i) _) l
        (𝓝 (spatialTensorOp (1 : H →L[ℂ] H) a _))
      simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self] using h
    | add x y hx hy =>
      simpa only [map_add, UniformSpace.Completion.coe_add] using hx.add hy

end

end KadisonKastler

end OAI
