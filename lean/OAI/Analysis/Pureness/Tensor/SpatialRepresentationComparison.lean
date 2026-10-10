import OAI.Analysis.Pureness.Tensor.SpatialFiniteCompression
import OAI.Analysis.Pureness.Tensor.FiniteTensorEnvelopes

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison CuntzTrace
open scoped TensorProduct InnerProductSpace CStarAlgebra

lemma operator_norm_bound_of_reconstruction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F →L[ℂ] E) (R : E →L[ℂ] F) (T : E →L[ℂ] E)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (v : E)
    (hv : L (R v) = v) (hTv : L (R (T v)) = T v) :
    ‖T v‖ ≤ ‖R.comp (T.comp L)‖ * ‖v‖ := by
  have hLc (x : F) : ‖L x‖ ≤ ‖x‖ :=
    (L.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg x))
  have hRc (x : E) : ‖R x‖ ≤ ‖x‖ :=
    (R.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hR (norm_nonneg x))
  calc
    ‖T v‖ = ‖L ((R.comp (T.comp L)) (R v))‖ := by simp [hv, hTv]
    _ ≤ ‖(R.comp (T.comp L)) (R v)‖ := hLc _
    _ ≤ ‖R.comp (T.comp L)‖ * ‖R v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hRc v) (norm_nonneg _)

variable {A B H H' K : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialStarTensor_norm_le_of_left_faithful
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (α' : A →⋆ₐ[ℂ] (H' →L[ℂ] H'))
    (hα' : Function.Injective α') (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ ≤ ‖spatialStarTensorHom α' β z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (spatialStarTensorHom α' β z)) ?_
  intro v
  induction v using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih v =>
    obtain ⟨w, hw⟩ := spatialStarTensor_preserves_algebraic α β z v
    obtain ⟨n, e, he, hv, hwfix⟩ := exists_finiteFrame_fix_tensors v w
    let L := spatialTensorMap (.id ℂ H) (finiteFrameSynthesis e)
    let R := spatialTensorMap (.id ℂ H) (finiteFrameSynthesis e).adjoint
    have hL : ‖L‖ ≤ 1 := spatialTensorMap_id_norm_le (finiteFrameSynthesis_norm_le e he)
    have hR : ‖R‖ ≤ 1 := spatialTensorMap_id_norm_le (finiteFrameSynthesis_adjoint_norm_le e he)
    have hLR (u : SpatialHilbert H K) :
        L (R u) = spatialTensorMap (.id ℂ H)
          ((finiteFrameSynthesis e).comp (finiteFrameSynthesis e).adjoint) u := by
      have h := spatialTensorMap_comp (.id ℂ H) (.id ℂ H)
        (finiteFrameSynthesis e) (finiteFrameSynthesis e).adjoint
      simpa [L, R] using congrArg (fun f => f u) h.symm
    have hb := operator_norm_bound_of_reconstruction L R (spatialStarTensorHom α β z)
      hL hR (v : SpatialHilbert H K) (by rw [hLR]; exact hv)
      (by rw [hw, hLR]; exact hwfix)
    have hc : ‖R.comp ((spatialStarTensorHom α β z).comp L)‖ ≤
        ‖spatialStarTensorHom α' β z‖ := by
      dsimp [L, R]
      rw [spatialFinite_compression]
      have hm : ‖spatialFinite α.toNonUnitalStarAlgHom n (finiteSpatialCoefficients β e z)‖ ≤
          ‖finiteSpatialCoefficients β e z‖ :=
        NonUnitalStarAlgHom.norm_apply_le (spatialFinite α.toNonUnitalStarAlgHom n) _
      exact hm.trans (finiteSpatialCoefficients_norm_le α' hα' β e he z)
    exact hb.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem spatialStarTensor_norm_eq_of_left_faithful
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (α' : A →⋆ₐ[ℂ] (H' →L[ℂ] H'))
    (hα : Function.Injective α) (hα' : Function.Injective α')
    (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ = ‖spatialStarTensorHom α' β z‖ :=
  le_antisymm (spatialStarTensor_norm_le_of_left_faithful α α' hα' β z)
    (spatialStarTensor_norm_le_of_left_faithful α' α hα β z)
end CuntzPureness

end

end OAI
