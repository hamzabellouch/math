import Mathlib

namespace OAI

                                     
section

/-! Quantitative radius parameter used by the chronological tiers in §07.
Constants are explicit and independent of the metric and the horizon. -/
namespace UniformKServer.TierParameters
noncomputable section

def cutoff (C h : ℝ) : ℕ := ⌈Real.exp (C*h)⌉₊

theorem cutoff_two (C h : ℝ) (hC : 1 ≤ C) (hh : 1 ≤ h) : 2 ≤ cutoff C h := by
  have ha : 1 ≤ C*h := by nlinarith
  have he := Real.add_one_le_exp (C*h)
  have hc := Nat.le_ceil (Real.exp (C*h))
  have : (2:ℝ) ≤ (cutoff C h : ℝ) := by unfold cutoff; linarith
  exact_mod_cast this

/-- The cutoff can be exponentially large in the tier, but the radius slope
is linear in that tier. No dependence on the number of records is introduced. -/
theorem radius_parameter (C h : ℝ) (hC : 1 ≤ C) (hh : 1 ≤ h) :
    Real.log (1+(cutoff C h:ℝ)^2) ≤ (2*C+4)*h := by
  have ha : 0 ≤ C*h := mul_nonneg (by linarith) (by linarith)
  have he : 1 ≤ Real.exp (C*h) := Real.one_le_exp_iff.mpr ha
  have hk0 : (0:ℝ) ≤ cutoff C h := Nat.cast_nonneg _
  have hk : (cutoff C h:ℝ) ≤ 2*Real.exp (C*h) := by
    have hc := Nat.ceil_lt_add_one (Real.exp_pos (C*h)).le
    unfold cutoff
    linarith
  have hs : (cutoff C h:ℝ)^2 ≤ (2*Real.exp (C*h))^2 :=
    pow_le_pow_left₀ hk0 hk 2
  have he2 : 1 ≤ (Real.exp (C*h))^2 := one_le_pow₀ he
  have harg : 1+(cutoff C h:ℝ)^2 ≤ 5*(Real.exp (C*h))^2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 1+(cutoff C h:ℝ)^2) harg
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_exp] at hl
  have h5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5)
    linarith
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith

end
end UniformKServer.TierParameters

end



end OAI
