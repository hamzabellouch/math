import OAI.NumberTheory.TotientAsymptotic.TailRenewal
import OAI.NumberTheory.TotientAsymptotic.PowerApproximation

namespace OAI

/-! Exponential limit of the finite-tail simplex factor, uniformly in phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma tailBudget_nonneg {x : ℝ} {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) (hm : H ≤ m x) : 0 ≤ tailBudget x H T := by
  unfold tailBudget
  apply add_nonneg (maxD_nonneg hT hm)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (g_pos _).le
  apply maxD_nonneg hT
  have hi := i.isLt
  unfold R at hi
  omega

/-- The exact power appearing in each intersection volume tends to its
phase-dependent exponential weight; no continuity in the phase is assumed. -/
theorem tail_simplex_power_limit (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ =>
      (max (1-tailBudget x H T/B x) 0)^(R x H) -
      Real.exp (-(gamma/alpha (theta x)) *
        ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)) atTop (nhds 0) := by
  let S := ∑' n : ℕ, rho^(H+n)*maxD (H+n) T
  let q : ℝ → ℝ := fun x => tailBudget x H T/B x
  let b : ℝ → ℝ := fun x => (gamma/alpha (theta x))*S
  let K := (gamma/lam)*S
  have hS : 0 ≤ S := tsum_nonneg (fun n =>
    mul_nonneg (pow_nonneg rho_pos.le _) (maxD_nonneg hT (by omega)))
  have hK : 0 ≤ K := mul_nonneg (div_pos gamma_pos lam_pos).le hS
  have hq : ∀ᶠ x : ℝ in atTop, 0 ≤ q x := by
    filter_upwards [m_tendsto.eventually (eventually_ge_atTop H),
      B_tendsto.eventually (eventually_gt_atTop 0)] with x hm hB
    exact div_nonneg (tailBudget_nonneg T hT hm) hB.le
  have hb : ∀ᶠ x : ℝ in atTop, 0 ≤ b x ∧ b x ≤ K := by
    filter_upwards [theta_eventually_mem] with x hx
    refine ⟨mul_nonneg (div_pos gamma_pos (alpha_pos _)).le hS, ?_⟩
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left gamma_pos.le lam_pos (alpha_ge_lam hx.1)) hS
  have hmerr : Tendsto (fun x => (m x : ℝ)*q x-b x) atTop (nhds 0) := by
    simpa only [q, b, S, mul_div_assoc] using tailBudget_exponent_error hford T hT
  have hbound : ∀ᶠ x : ℝ in atTop, (m x : ℝ)*q x ≤ K+1 := by
    filter_upwards [hmerr.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)), hb]
      with x he hb
    linarith
  have hq0 : Tendsto q atTop (nhds 0) := by
    apply squeeze_zero' hq
    · filter_upwards [hbound, m_tendsto.eventually (eventually_gt_atTop 0)] with x hx hm
      have hmR : (0 : ℝ) < m x := Nat.cast_pos.mpr hm
      show q x ≤ (K+1)*(m x : ℝ)⁻¹
      rw [← div_eq_mul_inv, le_div_iff₀ hmR]
      nlinarith
    · simpa using (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp m_tendsto)).const_mul (K+1)
  have hRerr : Tendsto (fun x => (R x H : ℝ)*q x-b x) atTop (nhds 0) := by
    have hh : Tendsto (fun x => (m x : ℝ)*q x-b x-(H : ℝ)*q x)
        atTop (nhds 0) := by
      simpa using hmerr.sub (hq0.const_mul (H : ℝ))
    apply hh.congr'
    filter_upwards [m_tendsto.eventually (eventually_ge_atTop H)] with x hm
    dsimp [R]
    rw [Nat.cast_sub hm]
    ring
  have hlim := simplex_power_approximation (fun x => R x H) q b K hK
    ((tendsto_sub_atTop_nat H).comp m_tendsto) hq hb hRerr
  simpa only [q, b, S, neg_mul] using hlim

end TotientAsymptotic

end

end OAI
