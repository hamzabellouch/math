import Mathlib

namespace OAI

namespace BorsukNine
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section PositiveSlice
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "M" => Matrix ν ν ℝ

noncomputable def unflattenMatrix : EuclideanSpace ℝ (ν × ν) →ₗ[ℝ] M where
  toFun x i j := x (i,j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def flatGram (x : EuclideanSpace ℝ (ν × ν)) : M :=
  unflattenMatrix x * (unflattenMatrix x)ᴴ

omit [DecidableEq ν] in
lemma flatGram_nonneg (x : EuclideanSpace ℝ (ν × ν)) : 0 ≤ flatGram x :=
  (Matrix.posSemidef_self_mul_conjTranspose _).nonneg

omit [DecidableEq ν] in
lemma flatGram_trace (x : EuclideanSpace ℝ (ν × ν)) : Matrix.trace (flatGram x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [flatGram,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,Fintype.sum_prod_type]
  simp only [pow_two]
  rfl

omit [DecidableEq ν] in
lemma flatGram_continuous : Continuous (flatGram (ν := ν)) := by
  have h := (unflattenMatrix (ν := ν)).continuous_of_finiteDimensional
  exact h.mul h.star

lemma positive_slice_image : {Q : M | 0 ≤ Q ∧ Matrix.trace Q = 1} =
    flatGram '' Metric.sphere (0 : EuclideanSpace ℝ (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : EuclideanSpace ℝ (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 = 1 := by rw [← flatGram_trace,hxQ,htr]
    have hnorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hnorm,hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hnorm : ‖x‖ = 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace,hnorm,one_pow]

lemma positive_slice_compact : IsCompact {Q : M | 0 ≤ Q ∧ Matrix.trace Q = 1} := by
  rw [positive_slice_image]
  exact (isCompact_sphere (0 : EuclideanSpace ℝ (ν × ν)) 1).image flatGram_continuous

end PositiveSlice
end BorsukNine

end OAI
