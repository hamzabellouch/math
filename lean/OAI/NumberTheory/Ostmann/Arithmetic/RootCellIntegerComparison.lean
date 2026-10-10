import OAI.NumberTheory.Ostmann.Arithmetic.OpenCellIntegerComparison
import OAI.NumberTheory.Ostmann.Arithmetic.RootCellPrimeComparison

namespace OAI

/-! # Root-cell idealization for the original external integer coordinate -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem root_cell_integer_comparison {q a : ℕ} (hq : 0 < q)
    (u v G : ℝ) (huv : u ≤ v) {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (c : (S → Ordering) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ code, ‖c code‖ ≤ C) :
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧ (∀ j, ‖d j‖ ≤ C) ∧
      ‖complexIntegerInterval q a u v G
          (fun y => c (rootCellCode S (Real.exp y)) * smoothPolynomialWeight F (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight F (Real.exp y) * (integerLogDensity q G y : ℂ)‖ ≤
        4 * ((S.card + 1 : ℕ) : ℝ) * C * smoothPolynomialBudget F * Real.exp (-G) := by
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  let d := fun j => c (rootCellCode S (Real.exp ((s j + s (j + 1)) / 2)))
  have hd (j : ℕ) : ‖d j‖ ≤ C := hc _
  refine ⟨s, N, d, hs, hs0, hsN, hN, hd, ?_⟩
  have herr : ‖complexIntegerInterval q a (s 0) (s N) G
        (fun y => c (rootCellCode S (Real.exp y)) * smoothPolynomialWeight F (Real.exp y)) -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        d j * smoothPolynomialWeight F (Real.exp y) * (integerLogDensity q G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖d j‖ * smoothPolynomialBudget F * (2 * Real.exp (-G)) +
          (2 * C * smoothPolynomialBudget F) * Real.exp (-G)) := by
    apply piecewise_integer_comparison q a hq G s hs N
      _ (fun j y => d j * smoothPolynomialWeight F (Real.exp y))
      (fun j => ‖d j‖ * smoothPolynomialBudget F) (fun _ => 2 * C * smoothPolynomialBudget F)
    · intro j hj
      exact continuousOn_const.mul
        (((continuous_smoothPolynomialWeight F).comp Real.continuous_exp).continuousOn)
    · intro j hj r hr M hr0 hrM
      rw [discreteVariation_const_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply smoothPolynomialWeight_variation_no_roots F (fun k => Real.exp (r k))
        (Real.exp_monotone.comp hr) M
      intro i x hx hxin
      apply hfree j hj x (hroots i x hx)
      refine ⟨?_, ?_⟩
      · simpa only [hr0] using hxin.1
      · have hlast : Real.exp (r (M - 1)) ≤ Real.exp (s (j + 1)) := by
          rw [← hrM]
          exact Real.exp_le_exp.mpr (hr (Nat.sub_le M 1))
        exact hxin.2.trans_le hlast
    · intro j hj
      exact mul_nonneg (mul_nonneg (by positivity) hC) (smoothPolynomialBudget_nonneg F)
    · intro j hj y hy
      calc
        _ ≤ ‖c (rootCellCode S (Real.exp y)) * smoothPolynomialWeight F (Real.exp y)‖ +
            ‖d j * smoothPolynomialWeight F (Real.exp y)‖ := norm_sub_le _ _
        _ ≤ C * smoothPolynomialBudget F + C * smoothPolynomialBudget F := by
          simp only [norm_mul]
          exact add_le_add
            (mul_le_mul (hc _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
            (mul_le_mul (hd _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
        _ = _ := by ring
    · intro j hj y hy
      congr 2
      apply rootCellCode_eq_of_root_free S (Real.exp (s j)) (Real.exp (s (j + 1)))
        (Real.exp y) (Real.exp ((s j + s (j + 1)) / 2)) (hfree j hj)
      · exact ⟨Real.exp_lt_exp.mpr hy.1, Real.exp_lt_exp.mpr hy.2⟩
      · constructor <;> apply Real.exp_lt_exp.mpr <;> linarith [hy.1, hy.2]
  rw [hs0, hsN] at herr
  apply herr.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range N, 4 * C * smoothPolynomialBudget F * Real.exp (-G) := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := mul_le_mul_of_nonneg_right (hd j) (smoothPolynomialBudget_nonneg F)
      have he := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 2 * Real.exp (-G))
      nlinarith
    _ = (N : ℝ) * (4 * C * smoothPolynomialBudget F * Real.exp (-G)) := by simp
    _ ≤ ((S.card + 1 : ℕ) : ℝ) * (4 * C * smoothPolynomialBudget F * Real.exp (-G)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hN)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC)
        (smoothPolynomialBudget_nonneg F)) (Real.exp_pos _).le
    _ = _ := by ring

end Ostmann

end OAI
