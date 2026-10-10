import OAI.NumberTheory.Ostmann.Arithmetic.HistoryUnnormalizedFlagErrorBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError
open Filter ScaleBudget

def commonLogBudget (T L : ℝ) : ℝ := T*(L+1)^2*Real.exp ((11/10000:ℝ)*L)
def totalLogCoefficient (N R T : ℝ) : ℝ := 3*T+N*(R+2)+1

theorem errorBudget_le_exp {N R T L A J D H : ℝ} {n : ℕ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hn : (n:ℝ) ≤ R*(L+1))
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hAQ : A ≤ Real.exp (commonLogBudget T L))
    (hJQ : J ≤ Real.exp (commonLogBudget T L))
    (hDQ : D ≤ Real.exp (commonLogBudget T L))
    (hHQ : H ≤ Real.exp (commonLogBudget T L)) :
    errorBudget A J D H (Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))) (Real.exp (N*L)) n ≤
      Real.exp (totalLogCoefficient N R T*(L+1)^2*Real.exp ((11/10000:ℝ)*L)-
        Real.exp ((39/10000:ℝ)*L)) := by
  have hb := errorBudget_le (n:=n) (atom:=Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))) hA hJ hD hH (Real.exp_nonneg _)
    (Real.one_le_exp (mul_nonneg hN hL)) (Real.exp_nonneg _) hAQ hJQ hDQ hHQ
  have ht : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  calc
    _ ≤ 2*(Real.exp (commonLogBudget T L))^3*
        Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))*(Real.exp (N*L))^(n+1) := hb
    _ ≤ Real.exp 1*(Real.exp (commonLogBudget T L))^3*
        Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))*(Real.exp (N*L))^(n+1) := by gcongr
    _ = Real.exp (1+3*commonLogBudget T L+N*L+((n+1:ℕ):ℝ)*(N*L)-
        Real.exp ((39/10000:ℝ)*L)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have he := polynomial_mass_exponent_le hL hN hR hT hn
      change 1+3*commonLogBudget T L+N*L+((n+1:ℕ):ℝ)*(N*L) ≤
        totalLogCoefficient N R T*(L+1)^2*Real.exp ((11/10000:ℝ)*L) at he
      linarith

theorem errorBudget_eventually (N R T : ℝ) (hN : 0 ≤ N) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (A J D H : ℝ),
      (n:ℝ) ≤ R*(L+1) →
      0 ≤ A → 0 ≤ J → 0 ≤ D → 0 ≤ H →
      A ≤ Real.exp (commonLogBudget T L) → J ≤ Real.exp (commonLogBudget T L) →
      D ≤ Real.exp (commonLogBudget T L) → H ≤ Real.exp (commonLogBudget T L) →
      errorBudget A J D H (Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))) (Real.exp (N*L)) n ≤
        Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  filter_upwards [eventually_double_exp_error (4*totalLogCoefficient N R T) 2
    (a:=11/10000) (b:=39/10000) (d:=1/500) (c:=1)
    (by norm_num) (by norm_num) (by norm_num), eventually_ge_atTop (1:ℝ)] with L he hL
  intro n A J D H hn hA hJ hD hH hAQ hJQ hDQ hHQ
  apply (errorBudget_le_exp hN hR hT (by linarith) hn hA hJ hD hH hAQ hJQ hDQ hHQ).trans
  apply le_trans _ he
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ totalLogCoefficient N R T := by unfold totalLogCoefficient; positivity
  have hquad : (L+1)^2 ≤ 4*L^2 := by nlinarith
  have hq := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hquad hc) (Real.exp_nonneg ((11/10000:ℝ)*L))
  nlinarith

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
