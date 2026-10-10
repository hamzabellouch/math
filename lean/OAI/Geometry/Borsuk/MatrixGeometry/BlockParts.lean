import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixFibre
import OAI.Geometry.Borsuk.Projectors.NegativeQuadratic

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockParts
variable {μ ν ι : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν] [Fintype ι]
local notation "W" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (𝕜 := ℝ)

omit [Nonempty ν] in
lemma matrixCompress_rankOne (e : W →ₗᵢ[ℝ] E) {c : E} (he : ∀ v, ⟪c,e v⟫ = 0) :
    matrixCompress e (rankOne c) = 0 := by
  apply (Matrix.toEuclideanCLM (n := μ) (𝕜 := ℝ)).injective
  apply ContinuousLinearMap.ext
  intro v
  change op (matrixCompress e (rankOne c)) v = op (0 : Matrix μ μ ℝ) v
  rw [matrixCompress_action,rankOne_action,he,zero_smul,map_zero,map_zero,
    zero_apply]

omit [Nonempty ν] in
lemma blockCorner_rankOne (e : W →ₗᵢ[ℝ] E) {c : E} (he : ∀ v, ⟪c,e v⟫ = 0) :
    blockCorner e (rankOne c) = 0 := by
  rw [blockCorner,matrixCompress_rankOne e he,map_zero]

omit [Nonempty ν] in
lemma block_decomposition {c : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0) :
    A = blockScalar c A • rankOne c + blockCorner e A := by
  have hAc : op A c = blockScalar c A • c := by
    have hd := frame_decomposition c e hc he hes (op A c)
    change e (blockOff c e A) = op A c - blockScalar c A • c at hd
    rw [hb,map_zero] at hd
    exact sub_eq_zero.mp hd.symm
  have hP := (rankOne_nonneg c).isSelfAdjoint
  have hB : IsSelfAdjoint (A - blockScalar c A • rankOne c) := hA.sub ((IsSelfAdjoint.all _).smul hP)
  have hk : op (A - blockScalar c A • rankOne c) c = 0 := by
    rw [map_sub,sub_apply,map_smul,smul_apply,
      rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul,hAc,sub_self]
  have hh := blockCorner_of_kernel e hes hB hk
  have hC : blockCorner e (A - blockScalar c A • rankOne c) = blockCorner e A := by
    simp only [blockCorner,map_sub,map_smul,matrixCompress_rankOne e he,smul_zero,sub_zero]
  rw [hC] at hh
  rw [hh]
  abel

lemma Admissible.signedExtension_nonpos {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≤ 0) : A ≤ 0 := by
  have hp (i : ι) : positiveExtension f A⁺ i = 0 := by
    apply le_antisymm _ (hf.positiveExtension_nonneg A⁺ i)
    apply le_of_not_gt
    intro h
    have hd := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    have hn := (mul_eq_zero.mp hd).resolve_left (ne_of_gt h)
    have hh := hs i
    simp only [signedExtension,Pi.sub_apply,hn,sub_zero] at hh
    exact (not_lt_of_ge hh) h
  have hz : A⁺ = 0 := matrix_psd_trace_zero (CFC.posPart_nonneg A) (by
    rw [← hf.positiveExtension_sum (CFC.posPart_nonneg A)]
    simp [hp])
  have he := CFC.posPart_sub_negPart A hA
  rw [hz,zero_sub] at he
  rw [← he]
  exact neg_nonpos.mpr (CFC.negPart_nonneg A)

omit [Nonempty ν] in
lemma block_parts {c : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    A⁺ = blockScalar c A • rankOne c ∧ A⁻ = -blockCorner e A := by
  have hk : op (-blockCorner e A) c = 0 := by
    rw [map_neg,neg_apply,blockCorner_kernel e he,neg_zero]
  have hp := rankOne_split_parts (neg_nonneg.mpr hC) hk ha (show (0:ℝ) ≤ 1 by norm_num)
  have heq : A = blockScalar c A • rankOne c - (1:ℝ) • (-blockCorner e A) := by
    rw [one_smul,sub_neg_eq_add]
    exact block_decomposition e hc he hes hA hb
  rw [← heq] at hp
  simpa only [one_smul] using hp

lemma Admissible.block_extension {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    signedExtension f A = blockScalar c A • f c + signedExtension f (blockCorner e A) := by
  obtain ⟨hp,hn⟩ := block_parts e hc he hes hA hb ha hC
  have hCp : (blockCorner e A)⁺ = 0 := (CFC.posPart_eq_zero_iff _ (blockCorner_selfAdjoint e hA)).mpr hC
  have hCn : (blockCorner e A)⁻ = -blockCorner e A := by
    have h := CFC.posPart_sub_negPart (blockCorner e A) (blockCorner_selfAdjoint e hA)
    rw [hCp,zero_sub] at h
    exact (neg_eq_iff_eq_neg.mp h)
  ext i
  simp only [signedExtension,Pi.sub_apply,hp,hn,hCp,hCn,positiveExtension_smul_nonneg f (rankOne_nonneg c) ha,
    hf.positiveExtension_rankOne c hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hz : positiveExtension f (0:M) = 0 := by
    simpa only [zero_smul] using positiveExtension_smul_nonneg f (Q := (0:M)) le_rfl (t := 0) le_rfl
  rw [hz]
  simp only [Pi.zero_apply,sub_eq_add_neg,zero_add]
end BlockParts
end BorsukNine

end OAI
