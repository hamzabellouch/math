import OAI.Analysis.Pureness.Tensor.SpatialTensorMaps
import OAI.Analysis.Pureness.Operators.FiniteHilbertFrames
import OAI.Analysis.Pureness.Comparison.SpatialFiniteMatrices

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison CuntzTrace
open scoped TensorProduct InnerProductSpace
variable {A B H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def finiteSpatialCoefficients (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) {n : ℕ} (e : Fin n → K) :
    A ⊗[ℂ] B →ₗ[ℂ] FinMatrix A n :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => CStarMatrix.ofMatrix (fun i j => inner ℂ (e i) (β b (e j)) • a)
          map_add' b c := by
            ext i j
            change inner ℂ (e i) (β (b + c) (e j)) • a =
              inner ℂ (e i) (β b (e j)) • a + inner ℂ (e i) (β c (e j)) • a
            simp [add_smul]
          map_smul' c b := by
            ext i j
            change inner ℂ (e i) (β (c • b) (e j)) • a =
              c • (inner ℂ (e i) (β b (e j)) • a)
            simp [smul_smul] }
      map_add' a c := by
        ext b i j
        change inner ℂ (e i) (β b (e j)) • (a + c) =
          inner ℂ (e i) (β b (e j)) • a + inner ℂ (e i) (β b (e j)) • c
        exact smul_add _ _ _
      map_smul' c a := by
        ext b i j
        change inner ℂ (e i) (β b (e j)) • (c • a) =
          c • (inner ℂ (e i) (β b (e j)) • a)
        exact smul_comm _ _ _ }

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteSpatialCoefficients_tmul (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) {n : ℕ}
    (e : Fin n → K) (a : A) (b : B) (i j : Fin n) :
    finiteSpatialCoefficients β e (a ⊗ₜ[ℂ] b) i j = inner ℂ (e i) (β b (e j)) • a := rfl

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialTensorOp_sum_right {ι : Type*} (s : Finset ι) (S : H →L[ℂ] H)
    (T : ι → K →L[ℂ] K) :
    spatialTensorOp S (∑ i ∈ s, T i) = ∑ i ∈ s, spatialTensorOp S (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, spatialTensorOp_add_right, ih]

omit [PartialOrder A] [StarOrderedRing A] in
theorem spatialFinite_compression
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (e : Fin n → K) (z : A ⊗[ℂ] B) :
    (spatialTensorMap (.id ℂ H) (finiteFrameSynthesis e).adjoint).comp
      ((spatialStarTensorHom α β z).comp
        (spatialTensorMap (.id ℂ H) (finiteFrameSynthesis e))) =
      spatialFinite α.toNonUnitalStarAlgHom n (finiteSpatialCoefficients β e z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp] using congrArg₂ (· + ·) hx hy
  | tmul a b =>
    have hc : (spatialTensorMap (.id ℂ H) (finiteFrameSynthesis e).adjoint).comp
        ((spatialTensorOp (α a) (β b)).comp
          (spatialTensorMap (.id ℂ H) (finiteFrameSynthesis e))) =
        spatialTensorOp (α a) ((finiteFrameSynthesis e).adjoint.comp
          ((β b).comp (finiteFrameSynthesis e))) := by
      apply spatialTensorMap_ext
      intro x y
      simp
    rw [spatialStarTensorHom_tmul, hc, finiteFrame_compression]
    change _ = spatialMatrixSum α.toNonUnitalStarAlgHom
      (fun i j => finiteSpatialCoefficients β e (a ⊗ₜ[ℂ] b) i j)
    simp only [spatialTensorOp_sum_right, spatialTensorOp_smul_right,
      spatialMatrixSum, spatialEntry, finiteSpatialCoefficients_tmul, map_smul,
      spatialTensorOp_smul_left]
    rfl

theorem finiteSpatialCoefficients_norm_le
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)
    (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) {n : ℕ} (e : Fin n → K)
    (he : Orthonormal ℂ e) (z : A ⊗[ℂ] B) :
    ‖finiteSpatialCoefficients β e z‖ ≤ ‖spatialStarTensorHom α β z‖ := by
  rw [← NonUnitalStarAlgHom.norm_map (spatialFinite α.toNonUnitalStarAlgHom n)
    (spatialFinite_injective α.toNonUnitalStarAlgHom hα n) (finiteSpatialCoefficients β e z), ← spatialFinite_compression α β e z]
  have hL := spatialTensorMap_id_norm_le (H := H) (finiteFrameSynthesis_norm_le e he)
  have hR := spatialTensorMap_id_norm_le (H := H) (finiteFrameSynthesis_adjoint_norm_le e he)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
  calc
    _ ≤ 1 * (‖spatialStarTensorHom α β z‖ * 1) := by gcongr
    _ = _ := by ring
end CuntzPureness

end

end OAI
