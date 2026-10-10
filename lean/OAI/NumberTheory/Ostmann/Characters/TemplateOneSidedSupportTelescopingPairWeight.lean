import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCore

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open Template
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

def copiedWindowRatio (T W : ℝ) (P : ℤ) : ℂ :=
  if Real.exp T*Real.exp (-W) ≤ (P:ℝ) ∧ (P:ℝ) ≤ Real.exp T*Real.exp W
    then (Real.exp T:ℂ)/(P:ℂ) else 0

theorem copiedWindowRatio_norm_le (T W : ℝ) (P : ℤ) :
    ‖copiedWindowRatio T W P‖ ≤ Real.exp W := by
  unfold copiedWindowRatio
  split_ifs with h
  · have hp : (0:ℝ)<P := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le h.1
    have he : Real.exp T ≤ Real.exp W*(P:ℝ) := by
      calc
        _ = Real.exp W*(Real.exp T*Real.exp (-W)) := by
          rw [←Real.exp_add,←Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h.1 (Real.exp_pos _).le
    have hn : ‖(P:ℂ)‖=(P:ℝ) := by
      rw [←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hn]
    exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using he)
  · rw [norm_zero]
    exact (Real.exp_pos _).le

def pairedHistoryMultiplier {ι : Type*} (k : ℕ)
    (mask : (j:ℕ)→ℤ→State k j→Prop) (X Δ W T Wc : ℝ)
    (j : ℕ) (s : Bool→ℤ) (x : Bool→(ι→ℤ)→State k j)
    (t : Bool→HistoryReconstruction.Tree j) (P : (ι→ℤ)→ℤ)
    (phase : (ι→ℤ)→ℂ) (a : ι→ℤ) : ℂ :=
  copiedWindowRatio T Wc (P a)*phase a*
    weight k mask X Δ W j (s false) (x false a) (t false)*
    conj (weight k mask X Δ W j (s true) (x true a) (t true))

theorem pairedHistoryMultiplier_norm_le {ι : Type*} (k : ℕ)
    (mask : (j:ℕ)→ℤ→State k j→Prop) (X Δ W T Wc : ℝ) (hX : 0<X)
    (j : ℕ) (s : Bool→ℤ) (x : Bool→(ι→ℤ)→State k j)
    (t : Bool→HistoryReconstruction.Tree j) (P : (ι→ℤ)→ℤ)
    (phase : (ι→ℤ)→ℂ) (a : ι→ℤ) (hphase : ‖phase a‖≤1) :
    ‖pairedHistoryMultiplier k mask X Δ W T Wc j s x t P phase a‖ ≤
      Real.exp Wc*(Arithmetic.leafFourierBound*Real.exp ((-Δ+W)/2))^(2^(j+1)) := by
  let B : ℝ := Arithmetic.leafFourierBound*Real.exp ((-Δ+W)/2)
  have hB : 0≤B := mul_nonneg Arithmetic.leafFourierBound_pos.le (Real.exp_pos _).le
  have hp := mul_le_mul (copiedWindowRatio_norm_le T Wc (P a)) hphase
    (norm_nonneg _) (Real.exp_pos Wc).le
  rw [mul_one] at hp
  have hl := weight_norm_le k mask X Δ W hX j (s false) (x false a) (t false)
  have hr := weight_norm_le k mask X Δ W hX j (s true) (x true a) (t true)
  unfold pairedHistoryMultiplier
  simp only [norm_mul,Complex.norm_conj]
  calc
    _ ≤ (Real.exp Wc*B^(2^j))*B^(2^j) :=
      mul_le_mul (mul_le_mul hp hl (norm_nonneg _) (Real.exp_pos _).le) hr
        (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (pow_nonneg hB _))
    _ = _ := by rw [mul_assoc,←pow_add]; congr 2; omega

theorem pairedHistoryMultiplier_norm_le_fixed {ι : Type*} (k : ℕ)
    (mask : (j:ℕ)→ℤ→State k j→Prop) (X Δ W T Wc : ℝ) (hX : 0<X) (hΔ : 0≤Δ)
    (j : ℕ) (s : Bool→ℤ) (x : Bool→(ι→ℤ)→State k j)
    (t : Bool→HistoryReconstruction.Tree j) (P : (ι→ℤ)→ℤ)
    (phase : (ι→ℤ)→ℂ) (a : ι→ℤ) (hphase : ‖phase a‖≤1) :
    ‖pairedHistoryMultiplier k mask X Δ W T Wc j s x t P phase a‖ ≤
      Real.exp Wc*(Arithmetic.leafFourierBound*Real.exp (W/2))^(2^(j+1)) := by
  apply (pairedHistoryMultiplier_norm_le k mask X Δ W T Wc hX j s x t P phase a hphase).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (mul_nonneg Arithmetic.leafFourierBound_pos.le (Real.exp_pos _).le)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) Arithmetic.leafFourierBound_pos.le

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
