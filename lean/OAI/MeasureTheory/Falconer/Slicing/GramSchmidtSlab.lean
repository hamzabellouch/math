import OAI.MeasureTheory.Falconer.Slicing.GramSchmidtMeasurable

namespace OAI

/-! # A small Gram--Schmidt residual lies in a fixed thin slab -/

namespace Falconer
open Set Submodule InnerProductSpace NormedSpace
open scoped BigOperators
variable {d : ℕ}

theorem inner_gramSchmidt_of_prefix_orthogonal (u : Space d) (v : Fin d → Space d)
    (i : Fin d) (h : ∀ j < i, inner ℝ u (v j) = 0) :
    inner ℝ u (gramSchmidt ℝ v i) = inner ℝ u (v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [gramSchmidt_def]
    simp only [inner_sub_right, inner_sum, starProjection_singleton, inner_smul_right,
      RCLike.ofReal_real_eq_id, id_eq]
    have hz : (∑ j ∈ Finset.Iio i,
        (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖ ^ 2) *
          inner ℝ u (gramSchmidt ℝ v j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ih j (Finset.mem_Iio.mp hj) (fun k hk => h k (hk.trans (Finset.mem_Iio.mp hj))),
        h j (Finset.mem_Iio.mp hj), mul_zero]
    rw [hz, sub_zero]

theorem exists_unit_prefix_normal (v : Fin d → Space d) (i : Fin d) :
    ∃ u : Space d, ‖u‖ = 1 ∧ ∀ j < i, inner ℝ u (v j) = 0 := by
  let b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) (E := Space d)
    (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v
  exact ⟨b i, b.orthonormal.1 i, fun j hj =>
    gramSchmidtOrthonormalBasis_inv_triangular _ v hj⟩

theorem small_residual_fixed_slab (v : Fin d → Space d) (i : Fin d) :
    ∃ u : Space d, ‖u‖ = 1 ∧ ∀ w : Fin d → Space d,
      (∀ j < i, w j = v j) → |inner ℝ u (w i)| ≤ ‖gramSchmidt ℝ w i‖ := by
  obtain ⟨u,hu,horth⟩ := exists_unit_prefix_normal v i
  refine ⟨u,hu,fun w hw => ?_⟩
  have he := inner_gramSchmidt_of_prefix_orthogonal u w i (fun j hj => by rw [hw j hj]; exact horth j hj)
  rw [← he]
  simpa only [hu,one_mul] using abs_real_inner_le_norm u (gramSchmidt ℝ w i)

theorem normalized_direction_slab (u c x : Space d) {R r : ℝ}
    (hx : ‖c-x‖ ≤ R) (hr : 0 ≤ r)
    (h : |inner ℝ u (normalize (c-x))| ≤ r) :
    |inner ℝ u x-inner ℝ u c| ≤ R*r := by
  have he : inner ℝ u (c-x) = ‖c-x‖*inner ℝ u (normalize (c-x)) := by
    nth_rw 1 [← norm_smul_normalize (c-x)]
    rw [inner_smul_right]
  calc
    _ = |inner ℝ u (c-x)| := by rw [inner_sub_right,abs_sub_comm]
    _ = ‖c-x‖*|inner ℝ u (normalize (c-x))| := by rw [he,abs_mul,abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖c-x‖*r := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ ≤ R*r := mul_le_mul_of_nonneg_right hx hr

end Falconer

end OAI
