import OAI.NumberTheory.Ostmann.Construction.NominalCenterSelectionRanges

namespace OAI

open Erdos970

namespace Ostmann.Construction.SourceRangeSeparation

theorem compensation_log_window (h J q w c z : ℝ) (hJ : 1000 ≤ J) (hh : h ≤ 2*J)
    (hw : |w-q*J| ≤ J/100) (hc : |c-w/4| ≤ h/500) (hz : |z-c| ≤ 1) :
    |z-q*J/4| ≤ J/100 := by
  obtain ⟨hw₁,hw₂⟩ := abs_le.mp hw
  obtain ⟨hc₁,hc₂⟩ := abs_le.mp hc
  obtain ⟨hz₁,hz₂⟩ := abs_le.mp hz
  apply abs_le.mpr
  constructor <;> linarith

theorem top_log_window (h J tb c z : ℝ) (hJ : 1000 ≤ J) (hh : h ≤ 2*J)
    (htb : |tb| ≤ h/16) (hc : |c-(J-2*tb)/6| ≤ h/500) (hz : |z-c| ≤ 1) :
    J/10 ≤ z ∧ z ≤ 9*J/40 := by
  obtain ⟨htb₁,htb₂⟩ := abs_le.mp htb
  obtain ⟨hc₁,hc₂⟩ := abs_le.mp hc
  obtain ⟨hz₁,hz₂⟩ := abs_le.mp hz
  constructor <;> linarith

theorem top_lt_compensation (J q x y : ℝ) (hJ : 0 < J) (hq : 1 ≤ q)
    (hx : x ≤ 9*J/40) (hy : |y-q*J/4| ≤ J/100) : x < y := by
  have hl := (abs_le.mp hy).1
  have hmul := mul_le_mul_of_nonneg_right hq hJ.le
  nlinarith

theorem compensation_lt_compensation (J : ℝ) (k a b : ℕ) (hab : a < b) (hb : b < k)
    (x y : ℝ) (hJ : 0 < J)
    (hx : |x-(2:ℝ)^(k-1-a)*J/4| ≤ J/100)
    (hy : |y-(2:ℝ)^(k-1-b)*J/4| ≤ J/100) : y < x := by
  have hexp : k-1-b+1 ≤ k-1-a := by omega
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hexp
  rw [pow_succ] at hp
  have hpow : (1:ℝ) ≤ 2^(k-1-b) := one_le_pow₀ (by norm_num)
  have hgap : 1 ≤ (2:ℝ)^(k-1-a)-(2:ℝ)^(k-1-b) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hgap hJ.le
  have hxl := (abs_le.mp hx).1
  have hyu := (abs_le.mp hy).2
  nlinarith

end Ostmann.Construction.SourceRangeSeparation

end OAI
