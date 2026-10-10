import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationErrorCap

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCompensationError
open Filter HistorySignedResidues

theorem selected_cap_error_eventually (Bs BD Bz C : ℝ) (k : ℕ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ J F : ℝ,
      0 ≤ J → J ≤ (actualFactorCap Bs BD Bz k L)^(4*l*2^l) →
      0 ≤ F → F ≤ Real.exp (rawLogBudget C L) →
      J*F*(30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))) ≤
        Real.exp (-Real.exp ((21/2000:ℝ)*L)) := by
  filter_upwards [weighted_error_eventually (compensationCost Bs BD Bz k (4*k*2^k)) C
    (compensationCost_nonneg Bs BD Bz k (4*k*2^k)) hC,
    eventually_ge_atTop (0:ℝ)] with L he hL
  intro l hl J F hJ hcap hF hFC
  exact he J F hJ (hcap.trans (actualFactorCap_pow_le Bs BD Bz k (4*k*2^k)
    (internalCount_le k l hl) hL)) hF hFC

theorem linear_le_rawLogBudget {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) :
    C*L ≤ rawLogBudget C L := by
  have hs : L ≤ (L+1)^2 := by nlinarith
  have he : 1 ≤ Real.exp ((1/100:ℝ)*L) := Real.one_le_exp (by positivity)
  have h := mul_le_mul_of_nonneg_left hs hC
  exact h.trans (le_mul_of_one_le_right (by positivity) he)

end Ostmann.Arithmetic.HistoryGiantCompensationError

end

end OAI
