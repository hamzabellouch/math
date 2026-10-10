import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.Rank
import OAI.Geometry.Borsuk.MatrixGeometry.PositiveSlice

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section MatrixFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma psd_inner_nonneg {Q : M} (hQ : 0 ≤ Q) (v : E) : 0 ≤ ⟪v,op Q v⟫ := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hQ).re_dotProduct_nonneg v.ofLp
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 ≤ ∑ i, (Q *ᵥ v.ofLp) i * v i
  simpa only [RCLike.re_to_real,dotProduct,Pi.star_apply,star_trivial,mul_comm] using h

lemma rankOne_mul_of_kernel {Q : M} (hQ : IsSelfAdjoint Q) {u : E}
    (hu : op Q u = 0) : rankOne u * Q = 0 := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (rankOne u * Q) = op 0
  rw [map_mul,map_zero]
  apply ContinuousLinearMap.ext
  intro v
  change op (rankOne u) (op Q v) = 0
  rw [rankOne_action]
  have hi : ⟪u,op Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint,← map_star,hQ.star_eq,hu,inner_zero_left]
  rw [hi,zero_smul]

lemma rankOne_split_parts {Q : M} (hQ : 0 ≤ Q) {u : E} (hu : op Q u = 0)
    {lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu) :
    (lam • rankOne u - mu • Q)⁺ = lam • rankOne u ∧
    (lam • rankOne u - mu • Q)⁻ = mu • Q := by
  apply CFC.posPart_negPart_unique rfl _ (smul_nonneg hl (rankOne_nonneg u)) (smul_nonneg hm hQ)
  rw [Matrix.smul_mul,Matrix.mul_smul,rankOne_mul_of_kernel hQ.isSelfAdjoint hu,smul_zero,smul_zero]

lemma nonunit_has_kernel (A : M) (hA : ¬ IsUnit A) :
    ∃ v : E, v ≠ 0 ∧ op A v = 0 := by
  have hdet : A.det = 0 := by
    by_contra h
    exact hA ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))
  obtain ⟨v,hv,hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨WithLp.toLp 2 v,fun h => hv (WithLp.toLp_injective 2 h),?_⟩
  rw [Matrix.toEuclideanCLM_toLp,hAv,WithLp.toLp_zero]

lemma fibre_boundary_kernel {Q : M} (hQ : 0 ≤ Q) (u : E)
    (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ v : E, ‖v‖ = 1 ∧ ⟪u,v⟫ = 0 ∧ op Q v = 0 := by
  obtain ⟨v,hv,hAv⟩ := nonunit_has_kernel _ hnot
  have hsum : ⟪v,op (rankOne u + Q) v⟫ = 0 := by rw [hAv,inner_zero_right]
  rw [map_add,add_apply,inner_add_right,rankOne_action,
    inner_smul_right,real_inner_comm u v] at hsum
  have hi : ⟪u,v⟫ = 0 := by
    nlinarith [psd_inner_nonneg hQ v,sq_nonneg ⟪u,v⟫]
  have hQv : op Q v = 0 := by
    simpa only [map_add,add_apply,rankOne_action,hi,zero_smul,zero_add] using hAv
  refine ⟨‖v‖⁻¹ • v,by simp [norm_smul,norm_inv,hv],?_,?_⟩
  · simp only [inner_smul_right,hi,mul_zero]
  · rw [map_smul,hQv,smul_zero]

noncomputable def matrixFibre (u : E) : Set M :=
  {Q | 0 ≤ Q ∧ Matrix.trace Q = 1 ∧ op Q u = 0}

lemma matrixFibre_compact (u : E) : IsCompact (matrixFibre u) := by
  have hop : Continuous (fun Q : M => op Q u) :=
    (((op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
  have he : matrixFibre u = {Q : M | 0 ≤ Q ∧ Matrix.trace Q = 1} ∩ {Q : M | op Q u = 0} := by
    ext Q
    simp only [matrixFibre,Set.mem_ofPred_eq,Set.mem_inter_iff,and_assoc]
  rw [he]
  exact positive_slice_compact.inter_right (isClosed_eq hop continuous_const)

end MatrixFibre
end BorsukNine

end OAI
