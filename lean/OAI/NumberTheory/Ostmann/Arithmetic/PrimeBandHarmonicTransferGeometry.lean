import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeBandHarmonicTransfer

def logDyadicIndex (x : ℝ) : ℕ := ⌊Real.log x/Real.log 2⌋₊

def logDyadicScale (j : ℕ) : ℝ := Real.exp ((j:ℝ)*Real.log 2)

lemma log_two_pos : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)

lemma logDyadicIndex_bounds {x : ℝ} (hx : 0<x) (hlog : 0≤Real.log x) :
    logDyadicScale (logDyadicIndex x)≤x ∧
      x<2*logDyadicScale (logDyadicIndex x) := by
  have hlo := Nat.floor_le (div_nonneg hlog log_two_pos.le)
  have hhi := Nat.lt_floor_add_one (Real.log x/Real.log 2)
  have hl : ((logDyadicIndex x:ℕ):ℝ)*Real.log 2≤Real.log x := by
    exact (le_div_iff₀ log_two_pos).mp hlo
  have hh : Real.log x<(((logDyadicIndex x:ℕ):ℝ)+1)*Real.log 2 := by
    exact (div_lt_iff₀ log_two_pos).mp hhi
  constructor
  · simpa only [logDyadicScale,Real.exp_log hx] using Real.exp_le_exp.mpr hl
  · have he := Real.exp_lt_exp.mpr hh
    rw [Real.exp_log hx,add_mul,one_mul,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] at he
    simpa only [logDyadicScale,mul_comm] using he

lemma logDyadicScale_lower {a x : ℝ} (ha : a≤Real.log x) :
    Real.exp (a-Real.log 2)≤logDyadicScale (logDyadicIndex x) := by
  have hf := (div_lt_iff₀ log_two_pos).mp (Nat.lt_floor_add_one (Real.log x/Real.log 2))
  apply Real.exp_le_exp.mpr
  change a-Real.log 2≤(⌊Real.log x/Real.log 2⌋₊:ℝ)*Real.log 2
  nlinarith

lemma logDyadicIndex_le {x b : ℝ} (hb : Real.log x≤b) :
    logDyadicIndex x≤⌊b/Real.log 2⌋₊ :=
  Nat.floor_mono (div_le_div_of_nonneg_right hb log_two_pos.le)

end Ostmann.Arithmetic.PrimeBandHarmonicTransfer

end

end OAI
