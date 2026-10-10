import OAI.NumberTheory.Ostmann.Supply.RetainedBandScales

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter

theorem supplyRadius_loglog_le {L : ℝ} (hL : 1≤L) :
    Real.log (Real.log (supplyRadius L:ℝ))≤L := by
  have he : (2:ℝ)≤Real.exp L := by have := Real.add_one_le_exp L; linarith
  have ha : (1:ℝ)≤Real.exp L/2 := by linarith
  have hexp : (2:ℝ)≤Real.exp (Real.exp L/2) := by
    have := Real.add_one_le_exp (Real.exp L/2)
    linarith
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos (Real.exp L/2)).le
  have hR : (supplyRadius L:ℝ)≤Real.exp (Real.exp L) := by
    unfold supplyRadius
    have hpow : Real.exp (Real.exp L/2)^2=Real.exp (Real.exp L) := by
      rw [←Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [←hpow]
    nlinarith
  have hR0 : (0:ℝ)<supplyRadius L := Nat.cast_pos.mpr (supplyRadius_pos L)
  have hR1 : (1:ℝ)<supplyRadius L := by
    have h := Nat.le_ceil (Real.exp (Real.exp L/2))
    change Real.exp (Real.exp L/2)≤(supplyRadius L:ℝ) at h
    linarith
  have hlog : Real.log (supplyRadius L:ℝ)≤Real.exp L := by
    simpa only [Real.log_exp] using Real.log_le_log hR0 hR
  simpa only [Real.log_exp] using Real.log_le_log (Real.log_pos hR1) hlog

theorem supplyRadius_le_double {L : ℝ} (_hL : 0≤L) :
    (supplyRadius L:ℝ)≤2*Real.exp (Real.exp L/2) := by
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos (Real.exp L/2)).le
  have he : 1≤Real.exp (Real.exp L/2) := Real.one_le_exp (by positivity)
  change (⌈Real.exp (Real.exp L/2)⌉₊:ℝ)≤_
  linarith

theorem product_le_common_budget {x y T a b : ℝ} (hx : 0≤x) (hy : 0≤y)
    (hT : 0≤T) (ha : 0≤a) (hb : 0≤b) (hxa : x^2≤T/a) (hyb : y^2≤T/b) :
    x*y≤T/Real.sqrt (a*b) := by
  have h1 : x≤Real.sqrt (T/a) := (Real.le_sqrt hx (div_nonneg hT ha)).mpr hxa
  have h2 : y≤Real.sqrt (T/b) := (Real.le_sqrt hy (div_nonneg hT hb)).mpr hyb
  calc
    _ ≤ Real.sqrt (T/a)*Real.sqrt (T/b) := mul_le_mul h1 h2 hy (Real.sqrt_nonneg _)
    _ = Real.sqrt ((T/a)*(T/b)) := (Real.sqrt_mul (div_nonneg hT ha) _).symm
    _ = Real.sqrt (T^2/(a*b)) := by congr 1; ring
    _ = T/Real.sqrt (a*b) := by rw [Real.sqrt_div (sq_nonneg T),Real.sqrt_sq hT]

end Ostmann.Supply

end

end OAI
