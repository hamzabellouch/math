import OAI.NumberTheory.JointDickman.Arithmetic.SieveRemainderDecay
import OAI.NumberTheory.JointDickman.Amplification.RegularityChernoffFactors

namespace OAI

/-! # Uniform control of the Markov multipliers on sieve remainders -/

namespace JointDickman

open Filter
open scoped Topology

theorem auxiliaryLogLength_between :
    ∀ᶠ B : ℕ in atTop, 0 ≤ auxiliaryLogLength B ∧ auxiliaryLogLength B ≤ Real.log B := by
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [auxiliaryLogLength_tendsto.eventually_ge_atTop 0,
    hloglarge, eventually_gt_atTop 1] with B hℓ hlog hB
  refine ⟨hℓ, ?_⟩
  have hr : auxiliaryRatio B = (B : ℝ) / Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    rfl
  have hRB : auxiliaryRatio B ≤ B := by
    rw [hr]
    exact div_le_self (Nat.cast_nonneg _) hlog
  exact Real.log_le_log (auxiliaryRatio_pos hB) hRB

theorem prefix_markov_multiplier_bounds {B : ℕ} {g τ s : ℝ}
    (hB : 1 ≤ B) (hg : 0 ≤ g) (hg1 : g ≤ 1) (hτ : 0 ≤ τ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hℓ : 0 ≤ auxiliaryLogLength B) (hℓlog : auxiliaryLogLength B ≤ Real.log B) :
    Real.exp (-s * ((g / 2 + τ) * auxiliaryLogLength B)) ≤ B ∧
    Real.exp (s * ((g / 2 - τ) * auxiliaryLogLength B)) ≤ B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hexp : Real.exp (Real.log B) = B := Real.exp_log hB0
  constructor
  · have hexponent : -s * ((g / 2 + τ) * auxiliaryLogLength B) ≤ Real.log B := by
      have hm := mul_nonneg hs (mul_nonneg (by linarith : 0 ≤ g / 2 + τ) hℓ)
      nlinarith
    exact (Real.exp_le_exp.mpr hexponent).trans_eq hexp
  · have hscoeff : s * (g / 2 - τ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (show g / 2 - τ ≤ 1 by linarith) hs
      nlinarith
    have h := mul_le_mul_of_nonneg_right hscoeff hℓ
    have hexponent : s * ((g / 2 - τ) * auxiliaryLogLength B) ≤ Real.log B := by nlinarith
    exact (Real.exp_le_exp.mpr hexponent).trans_eq hexp

theorem tail_markov_multiplier_bound {B Y C : ℝ} (hB : 1 ≤ B) (hY : 1 ≤ Y) (hC : 0 ≤ C) :
    Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C)) ≤ B := by
  have hB0 : 0 < B := by linarith
  have hY0 : 0 < Y := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hdiv : B / Y ≤ B := div_le_self hB0.le hY
  have hlogdiv := Real.log_le_log (div_pos hB0 hY0) hdiv
  have hexponent : (1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C) ≤ Real.log B := by linarith
  exact (Real.exp_le_exp.mpr hexponent).trans_eq (Real.exp_log hB0)

end JointDickman

end OAI
