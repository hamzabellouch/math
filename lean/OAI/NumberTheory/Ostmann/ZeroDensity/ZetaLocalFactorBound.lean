import OAI.NumberTheory.Ostmann.ZeroDensity.VonMangoldtLogarithmicBound

namespace OAI

/-! # Keeping the actual local zeta factors in the logarithmic-derivative bound -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zeta_local_log_budget : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    352 * (Real.log (96 * (|t| + 2) ^ 2) +
      (Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 + 1) ≤
        C * Real.log (|t| + 2) := by
  let D := 1 + Real.log 6 / Real.log (7 / 6 : ℝ)
  let E := Real.log 96 / Real.log 2 + 2
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  have h76 : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  have h96 : 0 < Real.log (96 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨352 * (D * E + 1 / Real.log 2), by positivity, ?_⟩
  intro t
  let L := Real.log (|t| + 2)
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num)
    (show (2 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
  have hone : 1 ≤ (1 / Real.log 2) * L := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ h2).mpr (by simpa using hL)
  have hconst : Real.log 96 ≤ (Real.log 96 / Real.log 2) * L := by
    have hh := mul_le_mul_of_nonneg_left hone h96.le
    convert hh using 1 <;> ring
  have hlog : Real.log (96 * (|t| + 2) ^ 2) = Real.log 96 + 2 * L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  have he : Real.log (96 * (|t| + 2) ^ 2) ≤ E * L := by
    rw [hlog]
    dsimp [E]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left he hD.le
  have hform : Real.log (96 * (|t| + 2) ^ 2) +
      (Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 =
        D * Real.log (96 * (|t| + 2) ^ 2) := by dsimp [D]; ring
  rw [hform]
  change _ ≤ 352 * (D * E + 1 / Real.log 2) * L
  nlinarith

theorem zeta_local_factor_bound : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (w : ℂ),
    ‖w‖ ≤ 5 / 4 → zetaAtHeight t w ≠ 0 →
    ‖logDeriv (zetaAtHeight t) w -
      ∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)‖ ≤
        C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, hbudget⟩ := zeta_local_log_budget
  refine ⟨C, hC, ?_⟩
  intro t w hw hfne
  obtain ⟨g, hg, he, hne⟩ := zeta_disk_quotient_exists t
  let M := 32 * (|t| + 2) ^ 2
  let N := ∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)
  let A := Real.log (3 * M) + N * Real.log 6 + 1
  have hA : 0 < A := by
    have hM : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t, sq_nonneg (|t| + 2)]
    have hl : 0 ≤ Real.log (3 * M) := Real.log_nonneg (by linarith)
    have hl6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
    have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    dsimp [A]
    positivity
  have hgb := logDeriv_norm_le_five_quarters_disk g A hA (fun z _ => hg z)
    (fun z hz => hne z (ball_subset_closedBall hz)) (fun z hz => ?_) w hw
  · have hwball : w ∈ closedBall 0 (3 / 2 : ℝ) := by
      simpa using hw.trans (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2)
    have hwS : w ∉ zetaDiskZeros t := fun hh => hfne ((mem_zetaDiskZeros t w).mp hh).2
    have hsplit : logDeriv (zetaAtHeight t) w =
        (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)) +
          logDeriv g w := by
      have hfun := funext he
      conv_lhs => rw [hfun]
      rw [logDeriv_fun_mul w (finiteZeroPolynomial_ne_zero _ _ w hwS) (hne w hwball)
        (finiteZeroPolynomial_analytic _ _ w).differentiableAt (hg w).differentiableAt,
        finiteZeroPolynomial_logDeriv _ _ w hwS]
    rw [hsplit, add_sub_cancel_left]
    have hmass := zetaDiskZeros_mass_bound t
    have hprod := mul_le_mul_of_nonneg_right hmass (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6))
    have hlog : Real.log (3 * M) = Real.log (96 * (|t| + 2) ^ 2) := by
      congr 1
      dsimp [M]
      ring
    apply hgb.trans
    apply le_trans _ (hbudget t)
    dsimp [A, N]
    rw [hlog]
    linarith
  · exact (zeta_disk_quotient_log_bound t M le_rfl g hg he hne z
      (by simpa using (mem_ball_iff_norm.mp hz).le)).trans (by dsimp [A, N]; linarith)

end Ostmann

end OAI
