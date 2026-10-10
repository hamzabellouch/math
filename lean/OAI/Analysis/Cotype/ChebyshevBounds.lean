import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev MeasureTheory
namespace Cotype

theorem chebyshev_abs_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(T ℝ n).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, T_real_cos]
  exact Real.abs_cos_le_one _

theorem chebyshev_derivative_zero_bound (n : ℕ) :
    |(T ℝ n).derivative.eval 0| ≤ n := by
  have hU := U_real_cos (Real.pi / 2) ((n : ℤ) - 1)
  have hUn : |(U ℝ ((n : ℤ)-1)).eval 0| ≤ 1 := by
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_one] at hU
    rw [hU]
    exact Real.abs_sin_le_one _
  rw [T_derivative_eq_U]
  simp only [eval_mul, Int.cast_natCast, eval_natCast, abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact (mul_le_mul_of_nonneg_left hUn (Nat.cast_nonneg n)).trans_eq (mul_one _)

theorem chebyshev_pairing_bound (Q : ℝ[X]) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ M) :
    |∫ x, Q.eval x * (T ℝ n).eval x ∂measureT| ≤ M * Real.pi := by
  rw [integral_measureT_eq_integral_cos]
  have hh : ∀ θ ∈ Set.uIoc (0 : ℝ) Real.pi,
      ‖Q.eval (Real.cos θ) * (T ℝ n).eval (Real.cos θ)‖ ≤ M := by
    intro θ _
    rw [Real.norm_eq_abs, abs_mul, T_real_cos]
    exact (mul_le_mul (hQ _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
      (Real.abs_cos_le_one _) (abs_nonneg _) hM).trans_eq (mul_one M)
  simpa [Real.norm_eq_abs, abs_of_pos Real.pi_pos] using
    intervalIntegral.norm_integral_le_of_norm_le_const hh

theorem chebyshev_pairing (i j : ℕ) :
    (∫ x, (T ℝ i).eval x * (T ℝ j).eval x ∂measureT) =
      if i = j then (if j = 0 then Real.pi else Real.pi/2) else 0 := by
  by_cases hij : i = j
  · subst i
    by_cases hj : j = 0
    · subst j
      simpa using integral_eval_T_real_mul_self_measureT_zero
    · simpa [hj] using integral_T_real_mul_self_measureT_of_ne_zero hj
  · simpa [hij] using integral_eval_T_real_mul_eval_T_real_measureT_of_ne hij

def chebyshevExpansion {d : ℕ} (c : Fin (d+1) → ℝ) : ℝ[X] :=
  ∑ j, c j • T ℝ (j : ℕ)

theorem chebyshevExpansion_pairing {d : ℕ} (c : Fin (d+1) → ℝ) (j : Fin (d+1)) :
    (∫ x, (chebyshevExpansion c).eval x * (T ℝ (j : ℕ)).eval x ∂measureT) =
      c j * (if (j : ℕ) = 0 then Real.pi else Real.pi/2) := by
  simp only [chebyshevExpansion, eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [mul_assoc, MeasureTheory.integral_const_mul, chebyshev_pairing]
    simp only [Fin.val_inj]
    simp
  · intro i _
    exact integrable_measureT (by fun_prop)

theorem chebyshevExpansion_coefficient_bound {d : ℕ} (c : Fin (d+1) → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M)
    (j : Fin (d+1)) : |c j| ≤ 2*M := by
  have hh := chebyshev_pairing_bound (chebyshevExpansion c) j hM hQ
  rw [chebyshevExpansion_pairing, abs_mul] at hh
  split_ifs at hh
  · rw [abs_of_pos Real.pi_pos] at hh
    nlinarith [Real.pi_pos]
  · rw [abs_of_pos (by positivity : 0 < Real.pi/2)] at hh
    nlinarith [Real.pi_pos]

theorem sum_fin_cast (d : ℕ) :
    (∑ j : Fin (d+1), (j : ℝ)) = (d : ℝ) * (d+1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem chebyshevExpansion_derivative_bound {d : ℕ} (c : Fin (d+1) → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M) :
    |(chebyshevExpansion c).derivative.eval 0| ≤ (d : ℝ) * (d+1) * M := by
  have he : (chebyshevExpansion c).derivative.eval 0 =
      ∑ j : Fin (d+1), c j * (T ℝ (j : ℕ)).derivative.eval 0 := by
    simp [chebyshevExpansion, eval_finsetSum]
  rw [he]
  calc
    _ ≤ ∑ j : Fin (d+1), |c j * (T ℝ (j : ℕ)).derivative.eval 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (d+1), (2*M) * (j : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (chebyshevExpansion_coefficient_bound c hM hQ j)
        (chebyshev_derivative_zero_bound j) (abs_nonneg _) (by positivity)
    _ = (d : ℝ) * (d+1) * M := by
      rw [← Finset.mul_sum, sum_fin_cast]
      ring

theorem exists_chebyshevExpansion (Q : ℝ[X]) (d : ℕ) (hdeg : Q.degree ≤ d) :
    ∃ c : Fin (d+1) → ℝ, chebyshevExpansion c = Q := by
  let S := chebyshevTsequence ℝ
  have hspan := S.span_degreeLE (m := d) (fun i _ =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero i)))
  have hRange : Set.range (fun i : Fin (d+1) => T ℝ (i : ℕ)) = S '' Set.Iic d := by
    ext P
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, Nat.le_of_lt_succ i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩
  have hm : Q ∈ Submodule.span ℝ (Set.range (fun i : Fin (d+1) => T ℝ (i : ℕ))) := by
    rw [hRange, hspan]
    exact mem_degreeLE.mpr hdeg
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hm
  exact ⟨c, hc⟩

theorem polynomial_derivative_zero_bound (Q : ℝ[X]) (d : ℕ) (hdeg : Q.degree ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hQ : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ M) :
    |Q.derivative.eval 0| ≤ (d : ℝ) * (d+1) * M := by
  obtain ⟨c, rfl⟩ := exists_chebyshevExpansion Q d hdeg
  exact chebyshevExpansion_derivative_bound c hM hQ

end Cotype

end

end OAI
