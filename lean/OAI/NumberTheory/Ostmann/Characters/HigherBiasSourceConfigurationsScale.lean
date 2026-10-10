import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Filter

def configurationCountCoefficient (β : ℝ) : ℝ := |β|+1

theorem configurationCountCoefficient_pos (β : ℝ) :
    0 < configurationCountCoefficient β := by
  unfold configurationCountCoefficient
  positivity

theorem configuration_count_exp_bound (β L : ℝ) (hL : 0 ≤ L) (e : ℕ) :
    (((2*⌊Real.exp (β*L)⌋₊+3)^e:ℕ):ℝ) ≤
      Real.exp (|β| *(e:ℝ)*L+(e:ℝ)*Real.log 5) := by
  have hf := Nat.floor_le (Real.exp_pos (β*L)).le
  have hm : β*L ≤ |β| *L := mul_le_mul_of_nonneg_right (le_abs_self β) hL
  have he := Real.exp_le_exp.mpr hm
  have h1 : 1 ≤ Real.exp (|β| *L) := Real.one_le_exp (mul_nonneg (abs_nonneg β) hL)
  have hb : ((2*⌊Real.exp (β*L)⌋₊+3:ℕ):ℝ) ≤ Real.exp (|β| *L+Real.log 5) := by
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<5)]
    push_cast
    nlinarith
  have hp := pow_le_pow_left₀ (show (0:ℝ)≤((2*⌊Real.exp (β*L)⌋₊+3:ℕ):ℝ) by positivity) hb e
  rw [←Real.exp_nat_mul] at hp
  push_cast at hp ⊢
  convert hp using 1
  congr 1
  ring

theorem eventually_configuration_count_bound (β : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ k N : ℕ,
      (((2*⌊Real.exp (β*L)⌋₊+3)^((k+1)*(N+1)+2*k):ℕ):ℝ) ≤
        Real.exp (configurationCountCoefficient β*((k+1)*(N+1)+2*k)*L) := by
  filter_upwards [eventually_ge_atTop (max 0 (Real.log 5))] with L hL k N
  have h0 := (le_max_left (0:ℝ) (Real.log 5)).trans hL
  have hlog := (le_max_right (0:ℝ) (Real.log 5)).trans hL
  apply (configuration_count_exp_bound β L h0 ((k+1)*(N+1)+2*k)).trans
  apply Real.exp_le_exp.mpr
  unfold configurationCountCoefficient
  have he : (0:ℝ) ≤ ((k+1)*(N+1)+2*k:ℕ) := Nat.cast_nonneg _
  push_cast at he ⊢
  nlinarith [mul_le_mul_of_nonneg_left hlog he]

end Ostmann.Characters.HigherBiasSource

end

end OAI
