import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaLocalFactorBound

namespace OAI

/-! # Quantitative local zeta bounds away from its actual zeros -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem zeta_local_mass_bound : ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
    (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)) ≤
      D * Real.log (|t| + 2) := by
  let D := (Real.log 96 / Real.log 2 + 2) / Real.log (7 / 6)
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h96 : 0 < Real.log (96 : ℝ) := Real.log_pos (by norm_num)
  have h76 : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro t
  have hL : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hconst : Real.log 96 ≤ (Real.log 96 / Real.log 2) * Real.log (|t| + 2) := by
    have hm := mul_le_mul_of_nonneg_left hL (div_nonneg h96.le h2.le)
    have he : (Real.log 96 / Real.log 2) * Real.log 2 = Real.log 96 := by field_simp
    rwa [he] at hm
  apply (zetaDiskZeros_mass_bound t).trans
  have hlog : Real.log (96 * (|t| + 2) ^ 2) = Real.log 96 + 2 * Real.log (|t| + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  rw [hlog]
  dsimp [D]
  apply (div_le_iff₀ h76).mpr
  have he : (Real.log 96 / Real.log 2 + 2) / Real.log (7 / 6) *
      Real.log (|t| + 2) * Real.log (7 / 6) =
      (Real.log 96 / Real.log 2 + 2) * Real.log (|t| + 2) := by field_simp
  rw [he]
  nlinarith

theorem zeta_local_logDeriv_separated : ∃ C : ℝ, 0 < C ∧
    ∀ (t : ℝ) (w : ℂ) (δ : ℝ), ‖w‖ ≤ 5 / 4 → zetaAtHeight t w ≠ 0 → 0 < δ →
      (∀ z ∈ zetaDiskZeros t, δ ≤ ‖w - z‖) →
      ‖logDeriv (zetaAtHeight t) w‖ ≤
        C * Real.log (|t| + 2) * (1 + δ⁻¹) := by
  obtain ⟨A, hA, ha⟩ := zeta_local_factor_bound
  obtain ⟨D, hD, hd⟩ := zeta_local_mass_bound
  refine ⟨A + D, by positivity, ?_⟩
  intro t w δ hw hne hδ hsep
  have hsum : ‖∑ z ∈ zetaDiskZeros t,
      (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)‖ ≤
        (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)) / δ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep z hz)
  have hmass := div_le_div_of_nonneg_right (hd t) hδ.le
  have he := norm_le_norm_sub_add (logDeriv (zetaAtHeight t) w)
    (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z))
  have herr := ha t w hw hne
  have hlog : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hAlog := mul_nonneg hA.le hlog
  have hDlog := mul_nonneg hD.le hlog
  have hAinv := mul_nonneg hAlog (inv_nonneg.mpr hδ.le)
  simp only [div_eq_mul_inv] at hmass hsum he herr
  nlinarith

end Ostmann

end OAI
