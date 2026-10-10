import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.SpectralMoment
import OAI.Probability.BinarySweep.MatrixBounds.TraceConvex

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalized_svd {q : ℕ} (hq : 0 < q) (A : M ι) (ht : 0 < matrixMoment q A) :
    ∃ (U V : M ι) (d : ι → ℝ), ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧
      (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
      A = (matrixMoment q A ^ ((2*q : ℕ) : ℝ)⁻¹ : ℝ) •
        (U * diagPower d ((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * V) := by
  obtain ⟨U, W, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  have hsum := matrixMoment_of_svd A q W s hg
  obtain ⟨hd, hsumd, heq⟩ := density_normalization (by omega : 0 < 2*q) s hs ht hsum.symm
  refine ⟨U, star (W : M ι), fun i => s i ^ (2*q) / matrixMoment q A,
    hU, ?_, hd, hsumd, ?_⟩
  · simpa only [norm_star] using unitary_norm_le_one W
  · conv_lhs => rw [hA, heq]
    simp only [mul_smul_comm, smul_mul_assoc]

lemma prod_ofFn_smul {m : ℕ} (r : Fin m → ℝ) (A : Fin m → M ι) :
    (List.ofFn (fun j => r j • A j)).prod = (∏ j, r j) • (List.ofFn A).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      rw [ih]
      rw [smul_mul_smul_comm]

lemma trace_diagonal_sandwich_pos {m : ℕ} (hm : 0 < m) (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (U V : Fin m → M ι) (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod‖ ≤ 1 := by
  cases m with
  | zero => omega
  | succ n => exact trace_diagonal_sandwich d hd hs x hx hsx U V hU hV

theorem matrix_trace_holder {q : ℕ} (hq : 0 < q) (A : Fin (2*q) → M ι) :
    ‖Matrix.trace (List.ofFn A).prod‖ ≤
      ∏ j, matrixMoment q (A j) ^ (((2*q : ℕ) : ℝ)⁻¹) := by
  classical
  have hm : 0 < 2*q := by omega
  have hm' : 0 < ((2*q : ℕ) : ℝ) := by exact_mod_cast hm
  by_cases hzero : ∃ j, matrixMoment q (A j) = 0
  · obtain ⟨j, hj⟩ := hzero
    have hAj : A j = 0 := (matrixMoment_eq_zero_iff hq (A j)).mp hj
    have hp : (List.ofFn A).prod = 0 := List.prod_eq_zero (List.mem_ofFn.mpr ⟨j, hAj⟩)
    rw [hp, Matrix.trace_zero, norm_zero]
    exact Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (matrixMoment_nonneg _ _) _)
  · have ht : ∀ j, 0 < matrixMoment q (A j) := by
      intro j
      exact lt_of_le_of_ne (matrixMoment_nonneg _ _) (Ne.symm (fun h => hzero ⟨j, h⟩))
    choose U V d hU hV hd hs heq using fun j => normalized_svd hq (A j) (ht j)
    let r : Fin (2*q) → ℝ := fun j => matrixMoment q (A j) ^ (((2*q : ℕ) : ℝ)⁻¹)
    let B : Fin (2*q) → M ι := fun j =>
      U j * diagPower (d j) (((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) * V j
    have hb : ‖Matrix.trace (List.ofFn B).prod‖ ≤ 1 := by
      apply trace_diagonal_sandwich_pos hm d hd hs (fun _ => ((2*q : ℕ) : ℝ)⁻¹)
        (fun _ => (inv_pos.mpr hm').le) _ U V hU hV
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ hm'.ne'
    have hEq : A = fun j => r j • B j := funext heq
    conv_lhs => rw [hEq, prod_ofFn_smul, Matrix.trace_smul, norm_smul]
    have hr : 0 ≤ ∏ j, r j := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (ht j).le _
    rw [Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hb

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
