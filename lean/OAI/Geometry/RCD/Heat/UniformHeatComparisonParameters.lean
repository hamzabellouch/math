import OAI.Geometry.RCD.Coordinates.NormalizationRebase
import OAI.Geometry.RCD.Heat.GaussianErrorBudget

namespace OAI

/-! # Uniform choices for the finite-range heat comparison -/

open Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

/-- The upper bound used by the actual heat comparison, rather than just
the split series itself, tends to zero with a small head and remote tail. -/
theorem exists_small_head_tail {a : ℕ → ℝ} (hpos : ∀ j, 0 ≤ a j)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ M, N ≤ M → ∀ e, 0 ≤ e → e ≤ ε →
      e * (∑' j, a j) + ∑' j, a (j + M) < η := by
  have hs : 0 ≤ ∑' j, a j := tsum_nonneg hpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_sum_nat_add a).eventually_lt_const (half_pos hη))
  let ε := η / (2 * ((∑' j, a j) + 1))
  have hε : 0 < ε := div_pos hη (by positivity)
  refine ⟨N, ε, hε, fun M hM e _ he => ?_⟩
  have hp : ε * (∑' j, a j) < η / 2 := by
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((∑' j, a j) + 1))).mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_right he hs
  linarith [hN M hM]

/-- One choice works simultaneously for all smaller radii, all later
finite normalization ranges and all smaller splitting errors. -/
theorem uniform_heat_comparison_parameters {a : ℕ → ℝ} (hpos : ∀ j, 0 ≤ a j)
    {C B lambda R η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ k, N ≤ k → ∀ e r,
      0 ≤ e → e ≤ ε → 0 ≤ r → r ≤ 1 → (2 : ℝ) ^ k * r ≤ R →
      C * Real.exp (B * r ^ 2) *
        (e * (∑' j, a j) + ∑' j, a (j + (k + 1))) +
        |lambda * r ^ 2| * (2 : ℝ) ^ k < η := by
  let F := C * Real.exp (max B 0)
  have hF : 0 ≤ F := mul_nonneg hC (Real.exp_pos _).le
  have htol : 0 < η / (2 * (F + 1)) := div_pos hη (by positivity)
  obtain ⟨N, ε, hε, hhead⟩ := exists_small_head_tail hpos htol
  have hdecay : Tendsto (fun k : ℕ => (|lambda| * R ^ 2) * (1 / 2 : ℝ) ^ k)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (|lambda| * R ^ 2)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hdecay.eventually_lt_const (half_pos hη))
  refine ⟨max N M, ε, hε, fun k hk e r he heε hr hr1 hR => ?_⟩
  have hbudget := hhead (k + 1)
    ((le_max_left N M).trans (hk.trans (Nat.le_succ k))) e he heε
  have hbudget0 : 0 ≤ e * (∑' j, a j) + ∑' j, a (j + (k + 1)) :=
    add_nonneg (mul_nonneg he (tsum_nonneg hpos)) (tsum_nonneg fun j => hpos _)
  have hexp : B * r ^ 2 ≤ max B 0 := by
    have hrsq : r ^ 2 ≤ 1 := by nlinarith
    by_cases hB : 0 ≤ B
    · have hb := mul_le_mul_of_nonneg_left hrsq hB
      simpa only [mul_one, max_eq_left hB] using hb
    · have hb : B * r ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hB) (sq_nonneg r)
      exact hb.trans (le_max_right _ _)
  have hcoef : C * Real.exp (B * r ^ 2) ≤ F :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
  have hsmall : F * (e * (∑' j, a j) + ∑' j, a (j + (k + 1))) < η / 2 := by
    have hm := mul_le_mul_of_nonneg_left hbudget.le hF
    have hb : F * (η / (2 * (F + 1))) < η / 2 := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (F + 1))).mpr
      nlinarith
    exact hm.trans_lt hb
  have hreg := dyadic_regularizer_le_geometric hr k hR (lambda := lambda)
  have hregsmall := hM k ((le_max_right N M).trans hk)
  have hmajor := mul_le_mul_of_nonneg_right hcoef hbudget0
  linarith

end RegularPointCoordinates

end

end OAI
