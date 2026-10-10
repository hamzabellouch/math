import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionAuxiliary

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

def parameterX (T : ℝ) : ℕ := ⌊Real.exp (T ^ (8 / 5 : ℝ))⌋₊

def auxiliaryExponent : ℝ := 1 / 10000000

def auxiliaryK (Z z : ℕ) : ℕ :=
  ⌊(1 / 50 : ℝ) * Real.log Z / Real.log (2 * (z : ℝ))⌋₊

def evenMomentParameter (X Z : ℕ) : ℕ :=
  2 * ⌈(Real.log X / Real.log Z + 10) / 2⌉₊

lemma evenMomentParameter_even (X Z : ℕ) : Even (evenMomentParameter X Z) := by
  unfold evenMomentParameter
  exact even_two_mul _

lemma evenMomentParameter_bounds (X Z : ℕ)
    (h : 0 ≤ Real.log X / Real.log Z + 10) :
    Real.log X / Real.log Z + 10 ≤ (evenMomentParameter X Z : ℝ) ∧
      (evenMomentParameter X Z : ℝ) < Real.log X / Real.log Z + 12 := by
  have hl := Nat.le_ceil ((Real.log X / Real.log Z + 10) / 2)
  have hu := Nat.ceil_lt_add_one (div_nonneg h (by norm_num : (0 : ℝ) ≤ 2))
  unfold evenMomentParameter
  push_cast
  constructor <;> linarith

lemma evenMomentParameter_least (X Z k : ℕ) (hk : Even k)
    (h : Real.log X / Real.log Z + 10 ≤ (k : ℝ)) :
    evenMomentParameter X Z ≤ k := by
  obtain ⟨m, rfl⟩ := hk
  have hceil : ⌈(Real.log X / Real.log Z + 10) / 2⌉₊ ≤ m := by
    apply Nat.ceil_le.mpr
    push_cast at h
    linarith
  unfold evenMomentParameter
  omega

lemma log_floor_exp_bounds {u : ℝ} (hu : Real.log 2 ≤ u) :
    1 ≤ ⌊Real.exp u⌋₊ ∧
      u - Real.log 2 ≤ Real.log (⌊Real.exp u⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp u⌋₊ : ℝ) ≤ u := by
  have hexp : (2 : ℝ) ≤ Real.exp u := (Real.log_le_iff_le_exp (by norm_num)).mp hu
  have hfloor := Nat.lt_floor_add_one (Real.exp u)
  have hhalf : Real.exp u / 2 ≤ (⌊Real.exp u⌋₊ : ℝ) := by linarith
  have hpos : (0 : ℝ) < (⌊Real.exp u⌋₊ : ℝ) :=
    lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) hhalf
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hpos.ne'), ?_, ?_⟩
  · have hlog := Real.log_le_log (div_pos (Real.exp_pos u) (by norm_num)) hhalf
    simpa only [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_exp] using hlog
  · simpa only [Real.log_exp] using
      Real.log_le_log hpos (Nat.floor_le (Real.exp_pos u).le)

lemma parameterX_tendsto : Tendsto parameterX atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)))

lemma eventually_mul_rpow_le_rpow (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ T : ℝ in atTop, C * T ^ a ≤ T ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C,
    eventually_gt_atTop (0 : ℝ)] with T hT hpos
  calc
    C * T ^ a ≤ T ^ (b - a) * T ^ a :=
      mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg hpos.le _)
    _ = T ^ b := by rw [← Real.rpow_add hpos]; congr 1; ring

lemma auxiliary_product_rpow_bound (Z z L : ℕ) (hZ : 1 ≤ Z) (hz : 1 ≤ z)
    (hL : L ≤ (2 * z) ^ auxiliaryK Z z) :
    (L : ℝ) ≤ (Z : ℝ) ^ (1 / 50 : ℝ) := by
  have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hzr : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hu : 0 < Real.log (2 * (z : ℝ)) := Real.log_pos (by linarith)
  have hv : 0 ≤ (1 / 50 : ℝ) * Real.log Z / Real.log (2 * (z : ℝ)) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hZr)) hu.le
  have hk : (auxiliaryK Z z : ℝ) ≤ (1 / 50 : ℝ) * Real.log Z /
      Real.log (2 * (z : ℝ)) := Nat.floor_le hv
  have hexp : Real.log (2 * (z : ℝ)) * (auxiliaryK Z z : ℝ) ≤
      Real.log (Z : ℝ) * (1 / 50 : ℝ) := by
    have hm := (le_div_iff₀ hu).mp hk
    nlinarith
  calc
    (L : ℝ) ≤ (2 * (z : ℝ)) ^ auxiliaryK Z z := by exact_mod_cast hL
    _ = Real.exp (Real.log (2 * (z : ℝ)) * (auxiliaryK Z z : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith : 0 < 2 * (z : ℝ))]
    _ ≤ Real.exp (Real.log (Z : ℝ) * (1 / 50 : ℝ)) := Real.exp_le_exp.mpr hexp
    _ = (Z : ℝ) ^ (1 / 50 : ℝ) :=
      (Real.rpow_def_of_pos (by linarith : (0 : ℝ) < Z) _).symm

end Ostmann.QuadraticCenter

end

end OAI
