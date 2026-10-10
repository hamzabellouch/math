import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.TraceHolder

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_pow_comm (A B : M ι) (q : ℕ) :
    Matrix.trace ((A * B)^q) = Matrix.trace ((B * A)^q) := by
  cases q with
  | zero => rfl
  | succ q =>
      rw [pow_succ, ← mul_assoc, mul_pow_mul, Matrix.trace_mul_comm,
        ← mul_assoc, ← pow_succ']

lemma matrixMoment_star (q : ℕ) (A : M ι) :
    matrixMoment q (star A) = matrixMoment q A := by
  simp only [matrixMoment, star_star]
  rw [trace_mul_pow_comm]

def schatten (q : ℕ) (A : M ι) : ℝ :=
  matrixMoment q A ^ (((2*q : ℕ) : ℝ)⁻¹)

lemma schatten_nonneg (q : ℕ) (A : M ι) : 0 ≤ schatten q A :=
  Real.rpow_nonneg (matrixMoment_nonneg _ _) _

lemma schatten_star (q : ℕ) (A : M ι) : schatten q (star A) = schatten q A := by
  simp only [schatten, matrixMoment_star]

lemma schatten_pow {q : ℕ} (hq : 0 < q) (A : M ι) :
    schatten q A ^ (2*q) = matrixMoment q A := by
  exact Real.rpow_inv_natCast_pow (matrixMoment_nonneg _ _) (by omega : 2*q ≠ 0)

lemma schatten_zero {q : ℕ} (hq : 0 < q) : schatten q (0 : M ι) = 0 := by
  rw [schatten, (matrixMoment_eq_zero_iff hq _).mpr rfl]
  exact Real.zero_rpow (inv_ne_zero (by exact_mod_cast (show 2*q ≠ 0 by omega)))

lemma prod_ofFn_sum {R κ : Type*} [Semiring R] [Fintype κ] {m : ℕ}
    (A : Fin m → κ → R) :
    (List.ofFn (fun j => ∑ k, A j k)).prod =
      ∑ f : Fin m → κ, (List.ofFn (fun j => A j (f j))).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.prod_cons, ih]
      rw [← (Fin.consEquiv (fun _ : Fin (m+1) => κ)).sum_comp, Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, List.prod_cons,
        Fin.cons_zero, Fin.cons_succ]

lemma trace_holder_sums {κ : Type*} [Fintype κ] {q : ℕ} (hq : 0 < q)
    (A : Fin (2*q) → κ → M ι) :
    ‖Matrix.trace (List.ofFn (fun j => ∑ k, A j k)).prod‖ ≤
      ∏ j, ∑ k, schatten q (A j k) := by
  rw [prod_ofFn_sum, Matrix.trace_sum]
  calc
    _ ≤ ∑ f : Fin (2*q) → κ, ‖Matrix.trace (List.ofFn (fun j => A j (f j))).prod‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f : Fin (2*q) → κ, ∏ j, schatten q (A j (f j)) := by
      exact Finset.sum_le_sum (fun f _ => matrix_trace_holder hq _)
    _ = ∏ j, ∑ k, schatten q (A j k) := by
      exact (Fintype.prod_sum (fun j k => schatten q (A j k))).symm

lemma prod_alternating {R : Type*} [Monoid R] (q : ℕ) (A B : R) :
    (List.ofFn (fun j : Fin (2*q) => if j.val % 2 = 0 then A else B)).prod =
      (A * B)^q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ]
      have hf : (fun j : Fin (2*q+2) => if j.val % 2 = 0 then A else B) =
          Fin.append (fun j : Fin (2*q) => if j.val % 2 = 0 then A else B)
            (fun j : Fin 2 => if j.val % 2 = 0 then A else B) := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp
        · simp [Nat.add_mod]
      rw [hf, List.ofFn_fin_append, List.prod_append, ih, pow_succ]
      simp [List.ofFn_succ]

lemma matrixMoment_le_sum_pow {κ : Type*} [Fintype κ] {q : ℕ} (hq : 0 < q)
    (A : κ → M ι) :
    matrixMoment q (∑ k, A k) ≤ (∑ k, schatten q (A k))^(2*q) := by
  let W : Fin (2*q) → κ → M ι :=
    fun j k => if j.val % 2 = 0 then star (A k) else A k
  have hW : (List.ofFn (fun j => ∑ k, W j k)).prod =
      (star (∑ k, A k) * (∑ k, A k))^q := by
    have heq : (fun j => ∑ k, W j k) =
        (fun j : Fin (2*q) => if j.val % 2 = 0 then star (∑ k, A k) else ∑ k, A k) := by
      funext j
      dsimp [W]
      split_ifs <;> simp [star_sum]
    rw [heq, prod_alternating]
  have hS : ∀ j : Fin (2*q), (∑ k, schatten q (W j k)) = ∑ k, schatten q (A k) := by
    intro j
    apply Finset.sum_congr rfl
    intro k _
    dsimp [W]
    split_ifs <;> simp only [schatten_star]
  have hh := trace_holder_sums hq W
  rw [hW] at hh
  simp only [hS, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hh
  exact (Complex.re_le_norm _).trans hh

theorem schatten_sum_le {κ : Type*} [Fintype κ] {q : ℕ} (hq : 0 < q)
    (A : κ → M ι) : schatten q (∑ k, A k) ≤ ∑ k, schatten q (A k) := by
  have hn : 0 ≤ ∑ k, schatten q (A k) := Finset.sum_nonneg fun k _ => schatten_nonneg _ _
  have hh := Real.rpow_le_rpow (matrixMoment_nonneg q (∑ k, A k))
    (matrixMoment_le_sum_pow hq A) (show 0 ≤ (((2*q : ℕ) : ℝ)⁻¹) by positivity)
  rw [Real.pow_rpow_inv_natCast hn (by omega : 2*q ≠ 0)] at hh
  exact hh

lemma matrix_one_norm_le : ‖(1 : M ι)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)

theorem trace_holder_contractions {q : ℕ} (hq : 0 < q)
    (A U V : Fin (2*q) → M ι) (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => U j * A j * V j)).prod‖ ≤
      ∏ j, schatten q (A j) := by
  have hm : 0 < 2*q := by omega
  have hm' : 0 < ((2*q : ℕ) : ℝ) := by exact_mod_cast hm
  by_cases hz : ∃ j, matrixMoment q (A j) = 0
  · obtain ⟨j, hj⟩ := hz
    have hAj : A j = 0 := (matrixMoment_eq_zero_iff hq _).mp hj
    have hp : (List.ofFn (fun j => U j * A j * V j)).prod = 0 := by
      apply List.prod_eq_zero
      exact List.mem_ofFn.mpr ⟨j, by simp [hAj]⟩
    rw [hp, Matrix.trace_zero, norm_zero]
    exact Finset.prod_nonneg fun k _ => schatten_nonneg _ _
  · have ht : ∀ j, 0 < matrixMoment q (A j) := by
      intro j
      exact lt_of_le_of_ne (matrixMoment_nonneg _ _) (Ne.symm (fun h => hz ⟨j,h⟩))
    choose S T d hS hT hd hs heq using fun j => normalized_svd hq (A j) (ht j)
    let C : Fin (2*q) → M ι := fun j =>
      (U j * S j) * diagPower (d j) (((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) * (T j * V j)
    have hc : ‖Matrix.trace (List.ofFn C).prod‖ ≤ 1 := by
      refine trace_diagonal_sandwich_pos hm d hd hs (fun _ => ((2*q : ℕ) : ℝ)⁻¹)
        (fun _ => (inv_pos.mpr hm').le) ?_ (fun j => U j*S j) (fun j => T j*V j) ?_ ?_
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_inv_cancel₀ hm'.ne'
      · intro j
        exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hU j)).trans (hS j))
      · intro j
        exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hT j)).trans (hV j))
    have hEq : (fun j => U j * A j * V j) = (fun j => schatten q (A j) • C j) := by
      funext j
      conv_lhs => rw [heq j]
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc, C, schatten]
    rw [hEq, prod_ofFn_smul, Matrix.trace_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun j _ => schatten_nonneg _ _)]
    exact mul_le_of_le_one_right (Finset.prod_nonneg fun j _ => schatten_nonneg _ _) hc

lemma matrixMoment_contraction_left {q : ℕ} (hq : 0 < q) (C A : M ι) (hC : ‖C‖ ≤ 1) :
    matrixMoment q (C*A) ≤ matrixMoment q A := by
  let W : Fin (2*q) → M ι := fun j => if j.val % 2 = 0 then star A else A
  let U : Fin (2*q) → M ι := fun j => if j.val % 2 = 0 then 1 else C
  let V : Fin (2*q) → M ι := fun j => if j.val % 2 = 0 then star C else 1
  have hU : ∀ j, ‖U j‖ ≤ 1 := by
    intro j; dsimp [U]; split_ifs
    · exact matrix_one_norm_le
    · exact hC
  have hV : ∀ j, ‖V j‖ ≤ 1 := by
    intro j; dsimp [V]; split_ifs
    · simpa only [norm_star] using hC
    · exact matrix_one_norm_le
  have heq : (fun j => U j * W j * V j) =
      (fun j : Fin (2*q) => if j.val % 2 = 0 then star (C*A) else C*A) := by
    funext j
    dsimp [U,W,V]
    split_ifs <;> simp only [one_mul, mul_one, star_mul]
  have hs : ∀ j, schatten q (W j) = schatten q A := by
    intro j; dsimp [W]; split_ifs <;> simp only [schatten_star]
  have hh := trace_holder_contractions hq W U V hU hV
  rw [heq, prod_alternating] at hh
  simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin, schatten_pow hq] at hh
  exact (Complex.re_le_norm _).trans hh

lemma schatten_contraction_left {q : ℕ} (hq : 0 < q) (C A : M ι) (hC : ‖C‖ ≤ 1) :
    schatten q (C*A) ≤ schatten q A :=
  Real.rpow_le_rpow (matrixMoment_nonneg _ _) (matrixMoment_contraction_left hq C A hC)
    (by positivity)

lemma matrixMoment_smul_real (q : ℕ) (r : ℝ) (A : M ι) :
    matrixMoment q (r • A) = r^(2*q) * matrixMoment q A := by
  simp only [matrixMoment, star_smul, star_trivial, smul_mul_smul_comm, smul_pow,
    Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [← sq, ← pow_mul]

lemma schatten_smul_nonneg {q : ℕ} (hq : 0 < q) {r : ℝ} (hr : 0 ≤ r) (A : M ι) :
    schatten q (r • A) = r * schatten q A := by
  unfold schatten
  rw [matrixMoment_smul_real, Real.mul_rpow (pow_nonneg hr _) (matrixMoment_nonneg _ _),
    Real.pow_rpow_inv_natCast hr (by omega : 2*q ≠ 0)]

theorem schatten_mul_le_op_left {q : ℕ} (hq : 0 < q) (A B : M ι) :
    schatten q (A*B) ≤ ‖A‖ * schatten q B := by
  by_cases hA : A = 0
  · simp [hA, schatten_zero hq]
  · have hn : 0 < ‖A‖ := norm_pos_iff.mpr hA
    let C : M ι := ‖A‖⁻¹ • A
    have hC : ‖C‖ ≤ 1 := by
      dsimp [C]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le),
        inv_mul_cancel₀ hn.ne']
    have heq : A*B = ‖A‖ • (C*B) := by
      dsimp only [C]
      rw [smul_mul_assoc, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [heq, schatten_smul_nonneg hq hn.le]
    exact mul_le_mul_of_nonneg_left (schatten_contraction_left hq C B hC) hn.le

theorem schatten_mul_le_op_right {q : ℕ} (hq : 0 < q) (A B : M ι) :
    schatten q (A*B) ≤ schatten q A * ‖B‖ := by
  have h := schatten_mul_le_op_left hq (star B) (star A)
  simpa only [← star_mul, schatten_star, norm_star, mul_comm] using h

lemma op_norm_le_schatten {q : ℕ} (hq : 0 < q) (A : M ι) : ‖A‖ ≤ schatten q A := by
  obtain ⟨U,V,s,hs,hU,hA,hg⟩ := exists_partial_svd A
  have ht := matrixMoment_of_svd A q V s hg
  have hd : ‖diagReal s‖ ≤ schatten q A := by
    rw [diagReal, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (schatten_nonneg _ _)).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs i)]
    have hi : s i^(2*q) ≤ matrixMoment q A := by
      rw [ht]
      exact Finset.single_le_sum (fun j _ => pow_nonneg (hs j) _) (Finset.mem_univ i)
    have h := Real.rpow_le_rpow (pow_nonneg (hs i) _) hi
      (show 0 ≤ (((2*q : ℕ) : ℝ)⁻¹) by positivity)
    rw [Real.pow_rpow_inv_natCast (hs i) (by omega : 2*q ≠ 0)] at h
    exact h
  calc
    ‖A‖ = ‖U * diagReal s * star (V : M ι)‖ := congrArg norm hA
    _ ≤ (‖U‖ * ‖diagReal s‖) * ‖star (V : M ι)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * schatten q A) * 1 := by
      apply mul_le_mul
      · exact mul_le_mul hU hd (norm_nonneg _) zero_le_one
      · simpa only [norm_star] using unitary_norm_le_one V
      · exact norm_nonneg _
      · exact mul_nonneg zero_le_one (schatten_nonneg _ _)
    _ = _ := by ring

theorem schatten_triple_le {q : ℕ} (hq : 0 < q) (A B C : M ι) :
    schatten q (A*B*C) ≤ schatten q A * ‖B‖ * schatten q C := by
  calc
    _ ≤ schatten q (A*B) * ‖C‖ := schatten_mul_le_op_right hq _ _
    _ ≤ (schatten q A * ‖B‖) * schatten q C :=
      mul_le_mul (schatten_mul_le_op_right hq A B) (op_norm_le_schatten hq C)
        (norm_nonneg _) (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _))

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
