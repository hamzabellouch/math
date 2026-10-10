import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module
open scoped Matrix InnerProductSpace
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma gram_mul_repr (b : Basis ι ℝ E) (u : E) :
    (Matrix.gram ℝ b) *ᵥ (fun i => b.repr u i) = fun i => inner ℝ (b i) u := by
  ext i
  calc
    _ = inner ℝ (b i) (∑ j, b.repr u j • b j) := by
      simp only [inner_sum,inner_smul_right,Matrix.mulVec,dotProduct,Matrix.gram_apply]
      simp only [mul_comm]
    _ = _ := by rw [b.sum_repr]

lemma inverse_gram_inner (b : Basis ι ℝ E) (u : E) :
    (Matrix.gram ℝ b)⁻¹ *ᵥ (fun i => inner ℝ (b i) u) = fun i => b.repr u i := by
  rw [← gram_mul_repr, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne')]
  simp

theorem inverse_gram_contraction (b : Basis ι ℝ E) (u v : E) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j) u * inner ℝ (b i) v =
      inner ℝ u v := by
  calc
    _ = ∑ i, b.repr u i * inner ℝ (b i) v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul]
      have hh := congrFun (inverse_gram_inner b u) i
      change (∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j) u) = b.repr u i at hh
      rw [hh]
    _ = inner ℝ (∑ i, b.repr u i • b i) v := by
      simp only [sum_inner,inner_smul_left,conj_trivial]
    _ = _ := by rw [b.sum_repr]

lemma inverse_gram_trace (b : Basis ι ℝ E) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b i) (b j) = Fintype.card ι := by
  have hh := Matrix.nonsing_inv_mul (Matrix.gram ℝ b)
    (isUnit_iff_ne_zero.mpr (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne')
  have ht := congrArg Matrix.trace hh
  simpa [Matrix.trace,Matrix.diag,Matrix.mul_apply,real_inner_comm] using ht


end

open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma lp_inverse_gram_fst_contraction (b : Basis ι ℝ (WithLp 2 (E×F))) (u v : E) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j).fst u * inner ℝ (b i).fst v = inner ℝ u v := by
  have h := inverse_gram_contraction b (WithLp.toLp 2 (u,(0:F))) (WithLp.toLp 2 (v,(0:F)))
  simpa [WithLp.prod_inner_apply] using h
lemma lp_inverse_gram_snd_contraction (b : Basis ι ℝ (WithLp 2 (E×F))) (u v : F) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j).snd u * inner ℝ (b i).snd v = inner ℝ u v := by
  have h := inverse_gram_contraction b (WithLp.toLp 2 ((0:E),u)) (WithLp.toLp 2 ((0:E),v))
  simpa [WithLp.prod_inner_apply] using h
lemma lp_inverse_gram_mixed_contraction (b : Basis ι ℝ (WithLp 2 (E×F))) (u : E) (v : F) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j).fst u * inner ℝ (b i).snd v = 0 := by
  have h := inverse_gram_contraction b (WithLp.toLp 2 (u,(0:F))) (WithLp.toLp 2 ((0:E),v))
  simpa [WithLp.prod_inner_apply] using h
lemma lp_inverse_gram_fst_trace [FiniteDimensional ℝ E] (b : Basis ι ℝ (WithLp 2 (E×F))) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j).fst (b i).fst = Module.finrank ℝ E := by
  let e := stdOrthonormalBasis ℝ E
  have h (x y : E) : inner ℝ x y = ∑ k, inner ℝ x (e k)*inner ℝ y (e k) := by
    rw [← e.sum_inner_mul_inner x y]
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm (e k) y]
  have h₁ (i j : ι) : inner ℝ (b j).fst (b i).fst =
      ∑ k, inner ℝ (b j).fst (e k)*inner ℝ (b i).fst (e k) := h _ _
  simp_rw [h₁,Finset.mul_sum]
  have hs : (∑ i, ∑ j, ∑ k, (Matrix.gram ℝ b)⁻¹ i j *
      (inner ℝ (b j).fst (e k)*inner ℝ (b i).fst (e k))) =
      ∑ k, ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
        (inner ℝ (b j).fst (e k)*inner ℝ (b i).fst (e k)) := by
    calc
      _ = ∑ i, ∑ k, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
          (inner ℝ (b j).fst (e k)*inner ℝ (b i).fst (e k)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hs]
  simp_rw [← mul_assoc,lp_inverse_gram_fst_contraction]
  simp [e.orthonormal.1]
lemma lp_inverse_gram_snd_trace [FiniteDimensional ℝ F] (b : Basis ι ℝ (WithLp 2 (E×F))) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j).snd (b i).snd = Module.finrank ℝ F := by
  let e := stdOrthonormalBasis ℝ F
  have h (x y : F) : inner ℝ x y = ∑ k, inner ℝ x (e k)*inner ℝ y (e k) := by
    rw [← e.sum_inner_mul_inner x y]
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm (e k) y]
  have h₁ (i j : ι) : inner ℝ (b j).snd (b i).snd =
      ∑ k, inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k) := h _ _
  simp_rw [h₁,Finset.mul_sum]
  have hs : (∑ i, ∑ j, ∑ k, (Matrix.gram ℝ b)⁻¹ i j *
      (inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k))) =
      ∑ k, ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
        (inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k)) := by
    calc
      _ = ∑ i, ∑ k, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
          (inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hs]
  simp_rw [← mul_assoc,lp_inverse_gram_snd_contraction]
  simp [e.orthonormal.1]

end YauCounterexamples
end

end OAI
