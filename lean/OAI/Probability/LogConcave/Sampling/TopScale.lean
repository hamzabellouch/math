import Mathlib
import OAI.Probability.LogConcave.Complexity.KernelAnalyticNormalizedBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

def topScale (κ : ℝ) (d : ℕ) : ℝ := (d:ℝ)^(-κ)/4
def proximalRounds (κ : ℝ) (d : ℕ) : ℕ := ⌈40*(1+κ)*dimensionLog d/topScale κ d⌉₊+1
def descentRounds (d : ℕ) : ℕ := ⌈20*dimensionLog d/Real.log 2⌉₊

lemma topScale_pos {κ : ℝ} {d : ℕ} (hd : 0<d) : 0<topScale κ d := by
  unfold topScale
  exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hd) _) (by norm_num)
lemma topScale_le_one {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) : topScale κ d≤1/4 := by
  unfold topScale
  exact div_le_div_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)) (by norm_num)
lemma topScale_rate (κ : ℝ) : LogPowerRate (topScale κ) κ := (LogPowerRate.power κ).div_const 4
lemma topScale_inv_rate (κ : ℝ) : LogPowerRate (fun d => (topScale κ d)⁻¹) (-κ) := by
  simpa only [topScale,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_comm] using (LogPowerRate.inv_power κ).const_mul 4

lemma LogPowerRate.natCeil {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (ha : a≤0)
    (hfp : ∀ᶠ d in atTop,0≤f d) : LogPowerRate (fun d => (⌈f d⌉₊:ℝ)) a := by
  apply LogPowerRate.of_le (hf.add ((LogPowerRate.const 1).mono ha))
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · filter_upwards [hfp] with d hd
    exact (Nat.ceil_lt_add_one hd).le

lemma proximalRounds_rate {κ : ℝ} (hκ : 0≤κ) :
    LogPowerRate (fun d => (proximalRounds κ d:ℝ)) (-κ) := by
  have hr := (LogPowerRate.log.const_mul (40*(1+κ))).mul (topScale_inv_rate κ)
  rw [zero_add] at hr
  have hc := LogPowerRate.natCeil hr (by linarith) (Eventually.of_forall (fun d => by dsimp [topScale]; positivity [dimensionLog_nonneg d,Real.rpow_nonneg (Nat.cast_nonneg d) (-κ)]))
  simpa only [proximalRounds,Nat.cast_add,Nat.cast_one,div_eq_mul_inv] using hc.add ((LogPowerRate.const 1).mono (by linarith))

lemma descentRounds_rate : LogPowerRate (fun d => (descentRounds d:ℝ)) 0 := by
  exact LogPowerRate.natCeil ((LogPowerRate.log.const_mul 20).div_const (Real.log 2)) le_rfl
    (Eventually.of_forall (fun d => by positivity [dimensionLog_nonneg d,Real.log_pos (by norm_num : (1:ℝ)<2)]))

lemma log_dimension_le {d : ℕ} (hd : 0<d) : Real.log (d:ℝ)≤dimensionLog d := by
  have hh := Real.log_le_log (by exact_mod_cast hd : (0:ℝ)<d) (by linarith : (d:ℝ)≤(d:ℝ)+1)
  unfold dimensionLog
  linarith

lemma proximalRounds_power {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) :
    (d:ℝ)^(20*(1+κ))≤(1+topScale κ d)^(proximalRounds κ d) := by
  let h := topScale κ d
  have hp : 0<h := topScale_pos (by omega)
  have hb : h≤1 := (topScale_le_one hκ hd).trans (by norm_num)
  have hl : h/2≤Real.log (1+h) := by
    have he := Real.le_log_one_add_of_nonneg hp.le
    have he' : h/2≤2*h/(h+2) := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    exact he'.trans he
  have hn : 40*(1+κ)*dimensionLog d/h≤(proximalRounds κ d:ℝ) := by
    have he := Nat.le_ceil (40*(1+κ)*dimensionLog d/h)
    dsimp [proximalRounds]
    push_cast
    linarith
  have hn' := (div_le_iff₀ hp).mp hn
  have hln := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (proximalRounds κ d) : (0:ℝ)≤_)
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  rw [Real.rpow_def_of_pos hd0]
  rw [←Real.exp_log (by positivity : 0<(1+h)^(proximalRounds κ d)),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (log_dimension_le (by omega : 0<d)) (by positivity : 0≤20*(1+κ))
  nlinarith

lemma descentRounds_power (d : ℕ) (hd : 1≤d) : (d:ℝ)^20≤(2:ℝ)^(descentRounds d) := by
  have hn := Nat.le_ceil (20*dimensionLog d/Real.log 2)
  have hp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hn' := (div_le_iff₀ hp).mp hn
  rw [←Real.exp_log (by positivity : 0<(d:ℝ)^20),Real.log_pow,
    ←Real.exp_log (by positivity : 0<(2:ℝ)^(descentRounds d)),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hd' := log_dimension_le (by omega : 0<d)
  dsimp [descentRounds]
  linarith

end LogConcaveSampling

end

end

end OAI
