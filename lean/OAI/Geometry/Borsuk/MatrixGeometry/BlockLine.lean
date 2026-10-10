import Mathlib
import OAI.Geometry.Borsuk.Support.NegativeFibre
import OAI.Geometry.Borsuk.MatrixGeometry.BlockParts

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped Matrix MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockLine
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν]
local notation "W" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (𝕜 := ℝ)
lemma positiveLine_eigenvector {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : op A c = lam • c := by
  rw [← CFC.posPart_sub_negPart A hA,map_sub,sub_apply,
    negPart_kernel_of_positiveLine hc hl hP,sub_zero,hP,map_smul,smul_apply,
    rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul]
lemma blockScalar_positiveLine {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockScalar c A = lam := by
  rw [blockScalar,positiveLine_eigenvector hA hc hl hP,inner_smul_right,real_inner_self_eq_norm_sq,hc,one_pow,mul_one]
omit [DecidableEq μ] in
lemma blockOff_positiveLine (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    blockOff c e A = 0 := by
  rw [blockOff,positiveLine_eigenvector hA hc hl hP,map_smul,adjoint_normal c e he,smul_zero]
lemma blockCorner_positiveLine (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockCorner e A = -A⁻ := by
  have hd := block_decomposition e hc he hes hA (blockOff_positiveLine e hA hc he hl hP)
  rw [blockScalar_positiveLine hA hc hl hP] at hd
  have hp := CFC.posPart_sub_negPart A hA
  rw [hP] at hp
  exact (add_left_cancel (show lam • rankOne c + -A⁻ = lam • rankOne c + blockCorner e A by simpa only [sub_eq_add_neg] using hp.trans hd)).symm

omit [Nonempty ν] in
lemma blockCompress_isUnit (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : E} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) (hb : blockOff c e A = 0) :
    IsUnit (matrixCompress e A) := by
  have hopU : IsUnit (op A) := IsUnit.map (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) hU
  have hAi : Function.Injective (op A) := (ContinuousLinearMap.isUnit_iff_bijective.mp hopU).1
  apply (isUnit_map_iff (op) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective (op (matrixCompress e A)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : op (matrixCompress e A) v = 0 := hv
    have hAv : op A (e v) = 0 := by
      conv_lhs => rw [block_decomposition e hc he hes hA hb]
      rw [map_add,add_apply,map_smul,smul_apply,
        rankOne_action,he,zero_smul,smul_zero,zero_add]
      change op (matrixEmbed e (matrixCompress e A)) (e v) = 0
      rw [show op (matrixEmbed e (matrixCompress e A)) (e v) = e (op (matrixCompress e A) v) from matrixEmbed_action e _ v,hv0,map_zero]
    apply e.injective
    exact hAi (by simpa only [map_zero] using hAv)
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩

lemma posDef_inner_pos {B : Matrix μ μ ℝ} (hB : B.PosDef) {v : W} (hv : v ≠ 0) :
    0 < ⟪v,op B v⟫ := by
  have hv' : v.ofLp ≠ 0 := fun h => hv (WithLp.ofLp_injective 2 h)
  have h := hB.dotProduct_mulVec_pos hv'
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 < ∑ i, (B *ᵥ v.ofLp) i * v i
  simpa only [dotProduct,Pi.star_apply,star_trivial,mul_comm] using h

lemma blockCompress_negative (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : E} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne c) : NegativeQuadratic (op (matrixCompress e A)) := by
  have hC := blockCorner_positiveLine e hA hc he hes hl hP
  have hcomp : -(matrixCompress e A) = matrixCompress e A⁻ := by
    have hh := congrArg (matrixCompress e) hC
    rw [blockCorner,matrixCompress_embed,map_neg] at hh
    exact neg_eq_iff_eq_neg.mpr hh
  have hn : 0 ≤ -(matrixCompress e A) := by rw [hcomp]; exact matrixCompress_nonneg e (CFC.negPart_nonneg A)
  have hunit := (blockCompress_isUnit e hA hU hc he hes (blockOff_positiveLine e hA hc he hl hP)).neg
  have hpd := (Matrix.nonneg_iff_posSemidef.mp hn).posDef_iff_isUnit.mpr hunit
  intro v hv
  have h := posDef_inner_pos hpd hv
  rw [map_neg,neg_apply,inner_neg_right] at h
  exact neg_pos.mp h
end BlockLine
end BorsukNine

end OAI
