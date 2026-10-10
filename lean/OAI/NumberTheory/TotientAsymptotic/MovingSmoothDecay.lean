import OAI.NumberTheory.TotientAsymptotic.MovingSmoothCutoff

namespace OAI

/-! The elementary decay estimates in the moving-smooth counting bound. -/
noncomputable section
namespace TotientAsymptotic

lemma moving_smooth_decay {b : ℝ} (hb : 0 ≤ b) :
    b*Real.exp (-60*b)*(Real.exp b)^4 ≤ Real.exp (-3*b) := by
  have hh : b ≤ Real.exp b := by linarith only [Real.add_one_le_exp b]
  have hp : (Real.exp b)^4=Real.exp (4*b) := by
    simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul b 4).symm
  calc
    _ ≤ Real.exp b*Real.exp (-60*b)*(Real.exp b)^4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le) (by positivity)
    _ = Real.exp (-55*b) := by
      rw [hp,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma exp_neg_triple_B {x : ℝ} (hx : 1 < x) :
    Real.exp (-3*B x) = ((Real.log x)^3)⁻¹ := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [show -3*B x=-(3*B x) by ring,Real.exp_neg]
  have hh : Real.exp (3*B x)=(Real.log x)^3 := by
    simpa only [Nat.cast_ofNat,B,Real.exp_log hl] using Real.exp_nat_mul (B x) 3
  rw [hh]

lemma moving_smooth_small_part {x : ℝ} (hx : 1 < x) (hB : 10000 ≤ B x) :
    Real.exp (Real.log x/2) ≤ x/(Real.log x)^3 := by
  have hb := (moving_smooth_budget hx hB).2.2.2.2
  have hh : Real.log x/2 ≤ Real.log x-3*B x := by linarith only [hb]
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_sub,Real.exp_log (by linarith : 0 < x)] at he
  have hpow : Real.exp (3*B x)=(Real.log x)^3 := by
    have hl := Real.log_pos hx
    simpa only [Nat.cast_ofNat,B,Real.exp_log hl] using Real.exp_nat_mul (B x) 3
  rwa [hpow] at he

end TotientAsymptotic

end

end OAI
