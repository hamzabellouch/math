import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPrimeAllRoots

namespace OAI

/-! # Prime comparison with the original sharp support gates retained -/

namespace Ostmann
open scoped Classical BigOperators
open MeasureTheory

/-- A sharp gate can change at every included polynomial root. Its exact values
at the roots are retained in the prime sum; endpoint atoms are part of the error. -/
theorem PublishedProgressionInput.gated_smooth_prime_all_roots (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexPrimeInterval q a u v (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc u v, w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      (S.card + 1 : ℕ) * (C * smoothPolynomialBudget F) *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)) := by
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  have h := P.common_root_prime_integral S s hs N hfree hQ hq hqQ ha
    (by simpa only [hs0] using hu) (by simpa only [hs0, hsN] using hshort)
    F hroots w C hC hw hconst
  simp only [hs0, hsN] at h
  have hlog : 0 ≤ Real.log (4 * (Q : ℝ)) := by
    apply Real.log_nonneg
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hB := smoothPolynomialBudget_nonneg F
  let E := 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
    Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)
  have hPC := P.errorConstant_nonneg
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  apply h.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range N, (C * smoothPolynomialBudget F) * E := by
      apply Finset.sum_le_sum
      intro j _
      have hj : u ≤ s j := by rw [← hs0]; exact hs (Nat.zero_le _)
      have ht : Real.exp (-P.decay * Real.sqrt (s j)) ≤ Real.exp (-P.decay * Real.sqrt u) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hj) (by linarith [P.decay_pos]))
      have hp : Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ))) ≤
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonpos_left hj (by linarith [P.kappa_pos])) hlog)
      have ha' : Real.exp (-(s j)) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (neg_le_neg hj)
      have he := add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left ht (show 0 ≤ 18 * P.errorConstant from mul_nonneg (by norm_num) hPC)) hp)
        (mul_le_mul_of_nonneg_left ha' (by norm_num : (0 : ℝ) ≤ 2))
      have hA : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
          Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ))) := by positivity
      calc
        _ ≤ C * smoothPolynomialBudget F *
              (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
                Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
              2 * C * smoothPolynomialBudget F * Real.exp (-(s j)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hw _) hB) hA) le_rfl
        _ = (C * smoothPolynomialBudget F) *
              ((18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
                Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) + 2 * Real.exp (-(s j))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hC hB)
    _ = (N : ℝ) * (C * smoothPolynomialBudget F) * E := by simp; ring
    _ ≤ (S.card + 1 : ℕ) * (C * smoothPolynomialBudget F) * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (mul_nonneg hC hB)) hE

end Ostmann

end OAI
