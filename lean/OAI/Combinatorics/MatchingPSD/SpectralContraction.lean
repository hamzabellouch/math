import OAI.Combinatorics.MatchingPSD.MatchingIncidence

namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def compression (A : Module.End ℝ E) (W : Submodule ℝ E) :
    Module.End ℝ W := W.orthogonalProjectionOnto.toLinearMap.comp (A.comp W.subtype)

lemma compression_symmetric (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) : (compression A W).IsSymmetric := by
  intro x y
  change ⟪W.orthogonalProjectionOnto (A x), y⟫ =
    ⟪x, W.orthogonalProjectionOnto (A y)⟫
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hA x y

lemma compression_inner (A : Module.End ℝ E) (W : Submodule ℝ E) (x y : W) :
    ⟪x, compression A W y⟫ = ⟪(x : E), A y⟫ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

omit [FiniteDimensional ℝ E] in
lemma trace_square_eq_sum_norm_sq (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {ι : Type u_2} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    LinearMap.trace ℝ E (A * A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, ← hA, real_inner_self_eq_norm_sq]

lemma trace_square_compression_le (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) :
    LinearMap.trace ℝ W (compression A W * compression A W) ≤
      LinearMap.trace ℝ E (A * A) := by
  classical
  let b := stdOrthonormalBasis ℝ W
  let e := stdOrthonormalBasis ℝ E
  rw [trace_square_eq_sum_norm_sq _ (compression_symmetric A hA W) b,
    trace_square_eq_sum_norm_sq A hA e]
  calc
    ∑ i, ‖compression A W (b i)‖ ^ 2 ≤ ∑ i, ‖A (b i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
        (W.norm_orthogonalProjectionOnto_apply_le _)
    _ = ∑ i, ∑ j, ⟪e j, A (b i)⟫ ^ 2 := by
      simp_rw [e.sum_sq_inner_right]
    _ = ∑ j, ∑ i, ⟪(b i : E), A (e j)⟫ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [← hA, real_inner_comm]
    _ ≤ ∑ j, ‖A (e j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hb := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
      have hh := hb.sum_inner_products_le (A (e j)) (s := Finset.univ)
      simpa only [Function.comp_apply, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Real.norm_eq_abs, sq_abs] using hh

end MatchingSmoothing

end OAI
