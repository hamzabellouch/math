import OAI.NumberTheory.Ostmann.Arithmetic.RootMeshIntegral

namespace OAI

/-! # Recombined prime comparison across all derivative roots -/

namespace Ostmann
open scoped Classical BigOperators
open MeasureTheory

/-- The root partition is internal to the proof. Both sides retain the entire
original interval, including its endpoint primes. -/
theorem PublishedProgressionInput.smooth_prime_all_roots (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S) :
    ‖complexPrimeInterval q a u v (fun y => smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc u v, smoothPolynomialWeight F (Real.exp y) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      (S.card + 1 : ℕ) * smoothPolynomialBudget F *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)) := by
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  have h := P.common_root_prime_integral S s hs N hfree hQ hq hqQ ha
    (by simpa only [hs0] using hu) (by simpa only [hs0, hsN] using hshort)
    F hroots (fun _ => 1) 1 (by norm_num) (by intro; simp) (by intros; rfl)
  simp only [one_mul, norm_one, hs0, hsN] at h
  have hlog : 0 ≤ Real.log (4 * (Q : ℝ)) := by
    apply Real.log_nonneg
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hB : 0 ≤ smoothPolynomialBudget F := smoothPolynomialBudget_nonneg F
  let E := 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
    Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)
  have hC := P.errorConstant_nonneg
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  apply h.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range N, smoothPolynomialBudget F * E := by
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
      have he := add_le_add
        (mul_le_mul_of_nonneg_left ht (show 0 ≤ 18 * P.errorConstant from mul_nonneg (by norm_num) hC)) hp
      have he' := mul_le_mul_of_nonneg_left he hB
      have he'' := mul_le_mul_of_nonneg_left ha' (show 0 ≤ 2 * smoothPolynomialBudget F from mul_nonneg (by norm_num) hB)
      dsimp only [E]
      nlinarith
    _ = (N : ℝ) * smoothPolynomialBudget F * E := by simp; ring
    _ ≤ (S.card + 1 : ℕ) * smoothPolynomialBudget F * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hB

end Ostmann

end OAI
