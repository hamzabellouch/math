import OAI.NumberTheory.CubicMoment.Estimates.IdealPrimeReplacement
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-! The exact prime-power deletion error has the classical square-root
size with two logarithms. -/
noncomputable section
namespace CubicFirstMoment

def idealPrimePowerErrorConstant : ℝ := 18*(1+1/Real.log 2)

lemma idealPrimePowerErrorConstant_pos : 0 < idealPrimePowerErrorConstant := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold idealPrimePowerErrorConstant
  positivity

lemma idealPrimePower_log_count {X : ℝ} (hX : Real.exp 1 ≤ X) :
    (Nat.log 2 ⌊X⌋₊+1:ℝ) ≤ (1+1/Real.log 2)*Real.log X := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hX
  have hL : 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hh
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX1)
  have hfloorpos : (0:ℝ) < (⌊X⌋₊:ℝ) := by exact_mod_cast (by omega : 0 < ⌊X⌋₊)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le hXp.le)
  have hn := Real.natLog_le_logb ⌊X⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh : (Nat.log 2 ⌊X⌋₊:ℝ) ≤ Real.log X/Real.log 2 :=
    hn.trans (div_le_div_of_nonneg_right hlog h2.le)
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem idealMangoldt_prime_replacement_log_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    ‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ ≤
      idealPrimePowerErrorConstant*Real.sqrt X*(Real.log X)^2 := by
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hX
  apply (idealMangoldt_prime_replacement_bound χ hχ hX1).trans
  have hh := mul_le_mul_of_nonneg_left (idealPrimePower_log_count hX)
    (show 0 ≤ 18*Real.sqrt X by positivity)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.log_nonneg hX1)
  convert hh' using 1
  simp only [idealPrimePowerErrorConstant]
  ring

end CubicFirstMoment

end

end OAI
