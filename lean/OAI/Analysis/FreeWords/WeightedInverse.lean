import Mathlib

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators

noncomputable section

theorem small_matrix_vector_bound {ι : Type*} [Fintype ι]
    (v r : ι → ℂ) (E : Matrix ι ι ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hcard : (Fintype.card ι : ℝ)*q ≤ 1/2)
    (hE : ∀ i k, ‖E i k‖ ≤ q) (hr : ∀ i, ‖r i‖ ≤ 1)
    (heq : ∀ i, v i+∑ k,E i k*v k=r i) : ‖v‖ ≤ 2 := by
  have hi (i : ι) : ‖v i‖ ≤ 1+(1/2)*‖v‖ := by
    have hv : v i=r i-∑ k,E i k*v k := by linear_combination heq i
    rw [hv]
    calc
      _ ≤ ‖r i‖+‖∑ k,E i k*v k‖ := norm_sub_le _ _
      _ ≤ 1+∑ k,‖E i k*v k‖ := add_le_add (hr i) (norm_sum_le _ _)
      _ ≤ 1+∑ k,q*‖v‖ := by
        gcongr with k
        rw [norm_mul]
        exact mul_le_mul (hE i k) (norm_le_pi_norm v k) (norm_nonneg _) hq
      _ = 1+((Fintype.card ι : ℝ)*q)*‖v‖ := by simp; ring
      _ ≤ _ := by gcongr
  have hnorm := (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1+(1/2 : ℝ)*‖v‖)).mpr hi
  linarith

theorem inverse_entry_bound_of_scaled_error {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (A B : Matrix ι ι ℂ) (hAB : A*B=1)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (j : ι) (hwj : w j=1)
    (hsmall : ∀ i k, ‖A i k*(w k : ℂ)/(w i : ℂ)-(if i=k then 1 else 0)‖ ≤
      (2*(Fintype.card ι : ℝ))⁻¹) : ∀ i, ‖B i j‖ ≤ 2*w i := by
  let v : ι → ℂ := fun i => B i j/(w i : ℂ)
  let E : Matrix ι ι ℂ := fun i k => A i k*(w k : ℂ)/(w i : ℂ)-(if i=k then 1 else 0)
  let r : ι → ℂ := fun i => (if i=j then 1 else 0)/(w i : ℂ)
  have hw0 (i : ι) : (w i : ℂ) ≠ 0 := by exact_mod_cast (hw i).ne'
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have heq (i : ι) : v i+∑ k,E i k*v k=r i := by
    have he := congrArg (fun T : Matrix ι ι ℂ => T i j) hAB
    simp only [Matrix.mul_apply,Matrix.one_apply] at he
    have hs : ∑ k,E i k*v k=(∑ k,A i k*B k j)/(w i : ℂ)-v i := by
      simp only [E,v,sub_mul,Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        field_simp [hw0]
      · simp
    rw [hs,he]
    simp [r]
  have hr (i : ι) : ‖r i‖ ≤ 1 := by
    by_cases hi : i=j
    · subst i; simp [r,hwj]
    · simp [r,hi]
  have hv : ‖v‖ ≤ 2 := small_matrix_vector_bound v r E _ (by positivity)
    (by field_simp; nlinarith) hsmall hr heq
  intro i
  have hvi := (norm_le_pi_norm v i).trans hv
  change ‖B i j/(w i : ℂ)‖ ≤ 2 at hvi
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw i)] at hvi
  exact (div_le_iff₀ (hw i)).mp hvi

end

end KKWeingarten
end

end OAI
