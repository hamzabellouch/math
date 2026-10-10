import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralIntegralGronwall

namespace OAI

/-! Remove the same-channel action before applying Gronwall. This keeps the
integral of the WKB residual, rather than the length of the whole shell. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_action_gronwall (a b A : ℝ) (hab : a≤ b) (X g H : ℝ → ℝ)
    (hX : ContinuousOn X (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hH : ContinuousOn H (Icc a b)) (hg0 : ∀ r ∈ Icc a b, 0≤ g r)
    (hbound : ∀ r ∈ Icc a b,
      X r≤ A*Real.exp (H r)+∫ t in a..r, g t*Real.exp (H r-H t)*X t) :
    ∀ r ∈ Icc a b, X r≤ A*Real.exp (H r+∫ t in a..r, g t) := by
  let Y := fun r => Real.exp (-H r)*X r
  have hY : ContinuousOn Y (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn hH.neg).mul hX
  have hprod (r t : ℝ) :
      Real.exp (-H r)*(g t*Real.exp (H r-H t)*X t)=g t*Y t := by
    have he : Real.exp (-H r)*Real.exp (H r-H t)=Real.exp (-H t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [Y]
    calc
      _ = g t*(Real.exp (-H r)*Real.exp (H r-H t))*X t := by ring
      _ = _ := by rw [he]; ring
  have hYbound (r : ℝ) (hr : r ∈ Icc a b) : Y r≤ A+∫ t in a..r, g t*Y t := by
    have hb := mul_le_mul_of_nonneg_left (hbound r hr) (Real.exp_pos (-H r)).le
    have he : Real.exp (-H r)*Real.exp (H r)=1 := by
      rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    change Y r≤ _ at hb
    calc
      Y r ≤ Real.exp (-H r)*(A*Real.exp (H r)+∫ t in a..r, g t*Real.exp (H r-H t)*X t) := hb
      _ = A+∫ t in a..r, g t*Y t := by
        rw [mul_add,← mul_assoc, mul_comm (Real.exp (-H r)) A,mul_assoc,he,mul_one,
          ← intervalIntegral.integral_const_mul]
        congr 1
        exact intervalIntegral.integral_congr (fun t _ => hprod r t)
  intro r hr
  have hh := spectral_integral_gronwall a b A hab Y g hY hg hg0 hYbound r hr
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (H r)).le
  have he : Real.exp (H r)*Real.exp (-H r)=1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  change Real.exp (H r)*(Real.exp (-H r)*X r)≤ _ at hm
  rw [← mul_assoc,he,one_mul] at hm
  calc
    X r ≤ Real.exp (H r)*(A*Real.exp (∫ t in a..r, g t)) := hm
    _ = _ := by rw [← mul_assoc,mul_comm (Real.exp (H r)) A,mul_assoc,← Real.exp_add]

end DefocusingNLS

end OAI
