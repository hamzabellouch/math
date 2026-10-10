import OAI.NumberTheory.Ostmann.ZeroDensity.ActualPageUniqueness

namespace OAI

/-! # Progression estimates and the Page theorem

The fields specify exceptional zeros and the prime progression estimate from
Montgomery–Vaughan, Theorem 11.3 and Corollary 11.20. Page uniqueness is
Corollary 11.10.
-/

namespace Ostmann

structure PublishedProgressionEstimate where
  kappa : ℝ
  decay : ℝ
  errorConstant : ℝ
  kappa_pos : 0 < kappa
  decay_pos : 0 < decay
  errorConstant_nonneg : 0 ≤ errorConstant
  localZero : ℕ → Option PrimitiveRealZero
  divides : ∀ q e, localZero q = some e → e.modulus ∣ q
  complete : ∀ q, 1 ≤ q → ∀ e : PrimitiveRealZero, e.modulus ∣ q →
    1 - kappa / Real.log (4 * (q : ℝ)) ≤ e.beta → localZero q = some e
  theta : ∀ q, 1 ≤ q → ∀ a, a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |primeProgressionTheta q a x -
      thetaMainTerm (Nat.totient q) (pageCoefficient (localZero q) a)
        (pageBeta (localZero q)) x| ≤
      errorConstant * x * Real.exp (-decay * Real.sqrt (Real.log x))

noncomputable def PublishedProgressionEstimate.toPublished
    (P : PublishedProgressionEstimate) : PublishedProgressionInput := by
  let κ := Classical.choose exists_actual_page_uniqueness
  have hκ := (Classical.choose_spec exists_actual_page_uniqueness).1
  have hpage := (Classical.choose_spec exists_actual_page_uniqueness).2
  exact {
    kappa := min P.kappa κ
    decay := P.decay
    errorConstant := P.errorConstant
    kappa_pos := lt_min P.kappa_pos hκ
    decay_pos := P.decay_pos
    errorConstant_nonneg := P.errorConstant_nonneg
    localZero := P.localZero
    divides := P.divides
    complete := by
      intro q hq e he hβ
      apply P.complete q hq e he
      have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hl : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
      have hh := div_le_div_of_nonneg_right (min_le_left P.kappa κ) hl.le
      linarith
    unique := by
      intro Q hQ e f he hf hβ hγ
      apply hpage Q hQ e f he hf
      all_goals
        have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
        have hl : 0 < Real.log (4 * (Q : ℝ)) := Real.log_pos (by linarith)
        have hh := div_le_div_of_nonneg_right (min_le_right P.kappa κ) hl.le
        linarith
    theta := P.theta }

end Ostmann

end OAI
