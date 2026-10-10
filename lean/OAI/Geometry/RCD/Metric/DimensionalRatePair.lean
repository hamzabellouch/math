import OAI.Geometry.RCD.Heat.EntropyPowerRateContinuous
import OAI.Analysis.RCDHeat.SignedEntropySupport

namespace OAI

/-! # Pairing the two dimensional evolution rates

The entropy ratios cancel by the weighted arithmetic-geometric mean
inequality. The remaining error records the difference of the square
roots of the two time speeds.
-/

open Set
noncomputable section
namespace RegularPointCoordinates

theorem hyperbolic_rate_quadratic_bound {q : ℝ} (hq : 0 < q) :
    q*(Real.cosh q-1)/Real.sinh q ≤ q^2/2 := by
  let f := fun x : ℝ => x*Real.sinh x-2*Real.cosh x+2
  have hd (x : ℝ) : HasDerivAt f (x*Real.cosh x-Real.sinh x) x := by
    convert (((hasDerivAt_id x).mul (Real.hasDerivAt_sinh x)).sub
      ((Real.hasDerivAt_cosh x).const_mul 2)).add_const 2 using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
    · exact (show Continuous f by unfold f; fun_prop).continuousOn
    · intro x _
      exact (hd x).hasDerivWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
      have hh := sinh_le_mul_cosh_real hx0.le
      linarith
  have hf := hm (show (0:ℝ) ∈ Ici 0 by simp) hq.le hq.le
  have hh : 2*(Real.cosh q-1) ≤ q*Real.sinh q := by
    dsimp only [f] at hf
    simp only [Real.sinh_zero,Real.cosh_zero,mul_zero,mul_one] at hf
    linarith only [hf]
  apply (div_le_iff₀ (Real.sinh_pos_iff.mpr hq)).mpr
  have hmul := mul_le_mul_of_nonneg_left hh hq.le
  nlinarith only [hmul]

theorem weighted_entropy_ratio_ge {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 < A) (hB : 0 < B) :
    2*Real.sqrt a*Real.sqrt b ≤ a*(B/A)+b*(A/B) := by
  have hh := sq_nonneg (Real.sqrt a*B-Real.sqrt b*A)
  rw [sub_sq,mul_pow,mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hb] at hh
  have he : a*(B/A)+b*(A/B)=(a*B^2+b*A^2)/(A*B) := by
    field_simp
  rw [he]
  apply (le_div_iff₀ (mul_pos hA hB)).mpr
  nlinarith only [hh]

theorem dimensional_rate_pair {N c a b A B : ℝ} (hN : 0 ≤ N) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 < A) (hB : 0 < B) :
    a*entropyPowerRate N c A B+b*entropyPowerRate N c B A ≤
      N*c*(a+b)/2+N*(Real.sqrt a-Real.sqrt b)^2 := by
  have hp := weighted_entropy_ratio_ge ha hb hA hB
  have he : a+b-(a*(B/A)+b*(A/B)) ≤ (Real.sqrt a-Real.sqrt b)^2 := by
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb]
  by_cases hc0 : c=0
  · simp only [entropyPowerRate,hc0,↓reduceIte,mul_zero,zero_mul,zero_div,zero_add]
    have hh := mul_le_mul_of_nonneg_left he hN
    nlinarith only [hh]
  · let q := Real.sqrt c
    have hq : 0 < q := Real.sqrt_pos.mpr (lt_of_le_of_ne hc (Ne.symm hc0))
    let r := q/Real.sinh q
    have hr : 0 ≤ r := div_nonneg hq.le (Real.sinh_pos_iff.mpr hq).le
    have hr1 : r ≤ 1 := (div_le_one (Real.sinh_pos_iff.mpr hq)).mpr (Real.self_le_sinh_iff.mpr hq.le)
    have hquad : q*(Real.cosh q-1)/Real.sinh q ≤ c/2 := by
      simpa only [q,Real.sq_sqrt hc] using hyperbolic_rate_quadratic_bound hq
    have hfirst := mul_le_mul_of_nonneg_left hquad (mul_nonneg hN (add_nonneg ha hb))
    have hsecond := mul_le_mul_of_nonneg_left he (mul_nonneg hN hr)
    have hthird := mul_le_mul_of_nonneg_right hr1 (sq_nonneg (Real.sqrt a-Real.sqrt b))
    have hthird' := mul_le_mul_of_nonneg_left hthird hN
    have hid : a*entropyPowerRate N c A B+b*entropyPowerRate N c B A =
        N*(a+b)*(q*(Real.cosh q-1)/Real.sinh q)+N*r*(a+b-(a*(B/A)+b*(A/B))) := by
      simp only [entropyPowerRate,hc0,↓reduceIte]
      dsimp only [q,r]
      ring
    rw [hid]
    nlinarith only [hfirst,hsecond,hthird']

end RegularPointCoordinates

end

end OAI
