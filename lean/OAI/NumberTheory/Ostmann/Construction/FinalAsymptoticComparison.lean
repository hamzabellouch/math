import OAI.NumberTheory.Ostmann.Construction.FinalHistoryComparison
import OAI.NumberTheory.Ostmann.Construction.FinalHistoryCount
import OAI.NumberTheory.Ostmann.Construction.FinalExponentialContradiction

namespace OAI

/-! # Closing the final comparison with its finite-depth frequency costs -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical
open Filter

theorem eventual_final_history_contradiction {Y A : Type*} [Fintype Y] [Fintype A]
    (n : ℕ) (Cfreq z α c B₁ D C : ℝ)
    (hCfreq : 0 ≤ Cfreq) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c)
    (hcost : 0 ≤ D + 2 * B₁ + 1)
    (hentropy : C + D + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ), 1 ≤ m → (m : ℝ) ≤ z * L →
      ∀ (P : Finset ℤ), (P.card : ℝ) ≤ Real.exp (Cfreq * m) →
      ∀ (ν : Y → ℝ) (μ : A → ℝ), (∀ y, 0 ≤ ν y) → (∀ a, 0 ≤ μ a) → (∑ a, μ a = 1) →
      (∑ y, ν y ≤ Real.exp (D * (2 ^ (n + 1) : ℝ) * m)) →
      ∀ a : FrequencyTree P n → (Y × ((ParityPathSum n × Fin m) → A)) → ℂ,
      (∑ x, finalBulkPrior n m ν μ x * ‖∑ h, a h x‖ ^ 2) ≤
        Real.exp (C * (2 ^ (n + 1) : ℝ) * m) →
      (∀ e f : FinalParityReassignments n m, e ≠ f → ∀ h k : FrequencyTree P n,
        ‖∑ x, (finalBulkPrior n m ν μ x : ℂ) *
          (a h (finalSamplePerm e x) * conj (a k (finalSamplePerm f x)))‖ ≤
            Real.exp (-c * Real.exp (α * L))) →
      Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤
        ‖∑ x, (finalBulkPrior n m ν μ x : ℂ) * (∑ h, a h x)‖ → False := by
  let r : ℝ := 2 ^ (n + 1)
  let K : ℝ := (D + 2 * B₁ + 1) * r
  have hK : 0 ≤ K := mul_nonneg hcost (by positivity)
  have hpoly := eventual_polynomial_log_budget K z α (c / 2) 1 hK hz hα (by positivity)
  filter_upwards [eventual_history_pair_decay n Cfreq z α c hCfreq hz hα hc, hpoly]
    with L hcount hpoly m hm hmL P hP ν μ hν hμ hμmass hmass a henergy hpair hlower
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hdecay := hcount (m : ℝ) P hm0 hmL hP
  have hlinear : (D + 2 * B₁ + 1) * r * m ≤ (c / 2) * Real.exp (α * L) := by
    have hp := hpoly (m : ℝ) hm0 hmL
    simp only [pow_one] at hp
    change K * m ≤ _
    nlinarith
  have herror : (Fintype.card (FrequencyTree P n) : ℝ) ^ 2 *
      Real.exp (-c * Real.exp (α * L)) ≤
        Real.exp (-(D + 2 * B₁ + 1) * (2 ^ (n + 1) : ℝ) * m) := by
    apply hdecay.trans
    apply Real.exp_le_exp.mpr
    dsimp only [r] at hlinear
    nlinarith
  have hcompare := final_history_comparison n m ν μ hν hμ hμmass
    (Real.exp (D * (2 ^ (n + 1) : ℝ) * m)) (Real.exp (C * (2 ^ (n + 1) : ℝ) * m))
    (Real.exp (-c * Real.exp (α * L))) hmass (Real.exp_nonneg _) Finset.univ a henergy
    (fun e f hef h _ k _ => hpair e f hef h k)
  simp only [Finset.card_univ] at hcompare
  have hlog : Real.log 2 < (1 : ℝ) := by
    have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hr : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmargin : Real.log 2 < 1 * (2 ^ (n + 1) : ℝ) * m := by nlinarith
  apply final_exponential_contradiction n m B₁ D C 1
    (Real.exp (D * (2 ^ (n + 1) : ℝ) * m))
    (Real.exp (C * (2 ^ (n + 1) : ℝ) * m))
    ((Fintype.card (FrequencyTree P n) : ℝ) ^ 2 * Real.exp (-c * Real.exp (α * L)))
    _ le_rfl (Real.exp_nonneg _) (by positivity) le_rfl herror hentropy hmargin hlower
  simpa only [card_finalParityReassignments] using hcompare

end Ostmann

end OAI
