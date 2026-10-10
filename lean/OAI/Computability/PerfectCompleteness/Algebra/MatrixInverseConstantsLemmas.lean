import Mathlib.Algebra.Order.Archimedean.Basic
import OAI.Computability.PerfectCompleteness.Foundations.GlobalityLemmas
import OAI.Computability.PerfectCompleteness.Foundations.LinearEvaluationLemmas

namespace OAI

section

namespace PerfectCompleteness.MatrixInverseConstants

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier UniqueGamesTheorem.Integration

theorem exists_cutoff_density {η : ℝ} (hη : 0 < η) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      MatrixLevelBridge.levelCutoffConstant r ρ +
        RankLevelFilter.node (r + 1) < η := by
  obtain ⟨q, hq, hqη⟩ := exists_pos_rat_lt hη
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < η / 2 by positivity)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let r : ℕ := n + 1
  have hn' : RankLevelFilter.node n < η / 2 := by
    simpa only [RankLevelFilter.node_eq_inv_pow, one_div, inv_pow] using hn
  have htail : RankLevelFilter.node (r + 1) < η / 2 :=
    (RankLevelFilter.node_antitone (show n ≤ r + 1 by dsimp [r]; omega)).trans_lt hn'
  obtain ⟨s, hs, hcut⟩ := CutoffBudget.exists_symbol_dimension_cutoff r hq
  have hρ := CutoffBudget.rho_real_bounds hs
  refine ⟨r, by dsimp [r]; omega, (FinalParameters.rho r s : ℝ), hρ.1, hρ.2, ?_⟩
  have hcut' :
      MatrixLevelBridge.levelCutoffConstant r (FinalParameters.rho r s : ℝ) ≤
        (q : ℝ) / 8 := by
    simpa only [MatrixLevelBridge.levelCutoffConstant, CutoffBudget.cutoffSum] using hcut
  linarith

end PerfectCompleteness.MatrixInverseConstants

end

section

namespace PerfectCompleteness.LowerRankParameters

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

theorem power_ratio_le {a b k : Nat} (h : a + k ≤ b) :
    (2 : ℝ) ^ a / (2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ k := by
  rw [div_pow, one_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [one_mul, ← pow_add] using
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h)

theorem exists_cross_parameters (r : Nat) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ m s : Nat, 0 < m ∧ 1 ≤ s ∧ ∀ s' : Nat, s ≤ s' →
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s' - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) < ρ := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (show 0 < ρ / 2 by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  let m := k + 3
  let s := 2 * r + m + k + 1
  refine ⟨m, s, by dsimp [m]; omega, by dsimp [s]; omega, ?_⟩
  intro s' hs'
  have hfirst : m + k ≤ s' - 2 * r := by dsimp [s] at hs'; omega
  have hsecond : 2 * m + k ≤ m * m := by dsimp [m]; nlinarith
  have h₁ := power_ratio_le hfirst
  have h₂ := power_ratio_le hsecond
  linarith

theorem exists_lower_parameters {η : ℝ} (hη : 0 < η) :
    ∃ r m s rowMinimum : Nat, 1 ≤ r ∧ 0 < m ∧ 1 ≤ s ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        MatrixLevelBridge.levelCutoffConstant r ρ + RankLevelFilter.node (r + 1) < η ∧
        (∀ ℓ, rowMinimum ≤ ℓ → 2 * m + r ≤ ℓ) ∧
        ∀ s', s ≤ s' →
          (2 : ℝ) ^ m / (2 : ℝ) ^ (s' - 2 * r) +
            (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) < ρ := by
  obtain ⟨r, hr, ρ, hρ, hρ', hcut⟩ := MatrixInverseConstants.exists_cutoff_density hη
  obtain ⟨m, s, hm, hs, herror⟩ := exists_cross_parameters r hρ
  exact ⟨r, m, s, 2 * m + r, hr, hm, hs, ρ, hρ, hρ', hcut,
    fun _ h => h, herror⟩

end PerfectCompleteness.LowerRankParameters

end

end OAI
