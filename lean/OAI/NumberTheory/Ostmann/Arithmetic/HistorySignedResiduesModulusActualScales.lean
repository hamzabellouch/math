import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualSources
import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion Filter

theorem actual_frequency_le_cap (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hm : 1 ≤ bulkSize k L) {j : ℕ} (hj : j ≤ k) :
    (frequencyBound Bs BD Bz k L j:ℝ) ≤ actualFactorCap Bs BD Bz k L := by
  apply (Nat.floor_le (Real.exp_pos _).le).trans
  apply Real.exp_le_exp.mpr
  apply (frequencyBudget_le_linear Bs BD Bz k L hm hj).trans
  have hC : scaleLinearConstant Bs BD Bz k ≤ actualFactorConstant Bs BD Bz k := by
    have hp : 0 ≤ 3*(2:ℝ)^k+1 := by positivity
    unfold actualFactorConstant
    linarith
  have hh := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg (bulkSize k L))
  have hp := actualFactorConstant_pos Bs BD Bz k
  have he := mul_nonneg hp.le (Real.exp_pos ((1/100:ℝ)*L)).le
  change _ ≤ actualFactorConstant Bs BD Bz k*((bulkSize k L:ℝ)+1) +
    actualFactorConstant Bs BD Bz k*Real.exp ((1/100:ℝ)*L)
  nlinarith

theorem spectator_le_actualFactorCap (Bs BD Bz : ℝ) (k : ℕ) {L : ℝ}
    (hL : 0 ≤ L) {p : ℕ} (hp : 0 < p)
    (hlog : Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) :
    (p:ℝ) ≤ actualFactorCap Bs BD Bz k L := by
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  rw [← Real.exp_log hp']
  apply Real.exp_le_exp.mpr
  have hs : Real.exp ((1/1000:ℝ)*L) ≤ Real.exp ((1/100:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hC : 1 ≤ actualFactorConstant Bs BD Bz k := by
    have hh := scaleLinearConstant_pos Bs BD Bz k
    unfold actualFactorConstant
    have hp : 0 ≤ (2:ℝ)^k := by positivity
    linarith
  have he := le_mul_of_one_le_left (Real.exp_pos ((1/100:ℝ)*L)).le hC
  have hm := mul_nonneg (actualFactorConstant_pos Bs BD Bz k).le
    (show 0 ≤ (bulkSize k L:ℝ)+1 by positivity)
  change _ ≤ actualFactorConstant Bs BD Bz k*((bulkSize k L:ℝ)+1) +
    actualFactorConstant Bs BD Bz k*Real.exp ((1/100:ℝ)*L)
  exact (hlog.trans hs).trans (by linarith)

theorem bulkSize_le_actualFactorCount (k : ℕ) (L : ℝ) :
    bulkSize k L ≤ actualFactorCount k L := by
  have hpow : 1 ≤ (2^k:ℕ) := Nat.one_le_pow _ _ (by omega)
  have hc : 1 ≤ (2^k:ℕ)*(6+4*k) := by
    simpa only [one_mul] using Nat.mul_le_mul hpow (show 1 ≤ 6+4*k by omega)
  have hh := Nat.mul_le_mul_right (bulkSize k L+1) hc
  exact (Nat.le_succ _).trans (by simpa only [one_mul, actualFactorCount] using hh)

theorem initial_spectator_count_le (k : ℕ) (L : ℝ) (spectator : PrimeSource)
    (x : Fin (2*(bulkSize k L/2)) → spectator.Sample) :
    (List.ofFn (fun i => (x i).val)).length ≤ actualFactorCount k L := by
  rw [List.length_ofFn]
  exact (by omega : 2*(bulkSize k L/2) ≤ bulkSize k L).trans (bulkSize_le_actualFactorCount k L)

theorem actual_log_budget_eventually (Bs BD Bz : ℝ) (k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop,
      A*((actualFactorCount k L:ℝ)+1)*Real.log (actualFactorCap Bs BD Bz k L) ≤
        Real.exp ((3/250:ℝ)*L) := by
  let F : ℝ := (2^k*(6+4*k):ℕ)
  let T : ℝ := bulkScale k+1
  let C : ℝ := actualFactorConstant Bs BD Bz k
  let D : ℝ := A*(F+1)*T*C*(T+1)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hT : 0 ≤ T := by dsimp [T,bulkScale]; positivity
  have hC : 0 ≤ C := (actualFactorConstant_pos Bs BD Bz k).le
  filter_upwards [ScaleBudget.eventually_poly_exp_le D 2
      (by norm_num : (1/100:ℝ) < 3/250) (by norm_num : (0:ℝ) < 1),
    eventually_ge_atTop (1:ℝ)] with L hpoly hL
  have hL0 : 0 ≤ L := by linarith
  have he : 1 ≤ Real.exp ((1/100:ℝ)*L) := Real.one_le_exp (by positivity)
  have hM : (bulkSize k L:ℝ)+1 ≤ T*L := by
    have hh := (bulkSize_bounds k hL0).2
    dsimp only [T]
    nlinarith
  have hN : (actualFactorCount k L:ℝ)+1 ≤ (F+1)*T*L := by
    have hc : (actualFactorCount k L:ℝ)+1 ≤ (F+1)*((bulkSize k L:ℝ)+1) := by
      have hn : (actualFactorCount k L:ℝ) = F*((bulkSize k L:ℝ)+1) := by
        simp only [actualFactorCount,F,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      rw [hn]
      nlinarith [show (0:ℝ) ≤ (bulkSize k L:ℝ) from Nat.cast_nonneg _]
    exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ F+1)])
  have hlog : Real.log (actualFactorCap Bs BD Bz k L) ≤
      C*(T+1)*L*Real.exp ((1/100:ℝ)*L) := by
    rw [actualFactorCap,Real.log_exp]
    change C*((bulkSize k L:ℝ)+1)+C*Real.exp ((1/100:ℝ)*L) ≤ _
    have h₁ := mul_le_mul_of_nonneg_left hM hC
    have h₂ := mul_le_mul_of_nonneg_left he (mul_nonneg hT hL0)
    have h₃ := mul_le_mul_of_nonneg_right hL (Real.exp_pos ((1/100:ℝ)*L)).le
    have h₂' := mul_le_mul_of_nonneg_left h₂ hC
    have h₃' := mul_le_mul_of_nonneg_left h₃ hC
    nlinarith
  have hlog0 : 0 ≤ Real.log (actualFactorCap Bs BD Bz k L) :=
    Real.log_nonneg (actualFactorCap_one_le Bs BD Bz k L)
  calc
    _ ≤ (A*((F+1)*T*L))*(C*(T+1)*L*Real.exp ((1/100:ℝ)*L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hN hA) hlog hlog0 (by positivity)
    _ = D*L^2*Real.exp ((1/100:ℝ)*L) := by dsimp [D]; ring
    _ ≤ _ := by simpa only [one_mul] using hpoly

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
