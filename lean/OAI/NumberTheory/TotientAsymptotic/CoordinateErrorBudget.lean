import OAI.NumberTheory.TotientAsymptotic.FullCoordinateCount

namespace OAI

/-! Quantitative absorption of the finite-grid error in a coordinate violation. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_root_budget {b ω u t m : ℝ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hu : 0 ≤ u) (ht : 0 ≤ t) (htb : t ≤ b)
    (hm : 0 ≤ m) (hsmall : u*m^6 ≤ ω^2*b/1000000) :
    m^3*Real.sqrt (u*t) ≤ ω*b/1000 := by
  have hsqrt := Real.sq_sqrt (mul_nonneg hu ht)
  have hs : (m^3*Real.sqrt (u*t))^2 ≤ (ω*b/1000)^2 := by
    calc
      _ = (u*m^6)*t := by rw [mul_pow,hsqrt]; ring
      _ ≤ (ω^2*b/1000000)*b :=
        mul_le_mul hsmall htb ht (by positivity)
      _ = _ := by ring
  have hleft : 0 ≤ m^3*Real.sqrt (u*t) := by positivity
  have hright : 0 ≤ ω*b/1000 := by positivity
  nlinarith

lemma coordinate_linear_budget {b ω L m : ℝ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hsmall : L*m^6 ≤ ω^2*b/1000000) :
    L*m^2 ≤ ω*b/1000000 := by
  have hpow : m^2 ≤ m^6 := pow_le_pow_right₀ hm (by norm_num)
  have h1 := mul_le_mul_of_nonneg_left hpow hL
  have hωsq : ω^2 ≤ ω := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right hωsq hb
  linarith

lemma coordinate_exponent_budget {b ω D L u : ℝ} {k K : ℕ}
    (hb : 1 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (_hD : 0 ≤ D)
    (hL : 0 ≤ L) (hu : 0 ≤ u) (huL : u ≤ L)
    (hK : (K:ℝ) ≤ b) (hKlo : b-Real.log (20*b)-2 ≤ K)
    (hsmall : L*((k:ℝ)+2)^6 ≤ ω^2*b/1000000)
    (hbudget : (Real.log (20*b)+9+D+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100) :
    Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1)-(1+ω)*b+
      (b+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*u+D*((k:ℝ)+2)^2+
      ((k:ℝ)+2)^3*Real.sqrt (u*K) ≤ -(1+ω/2)*b := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hKn : 0 ≤ (K:ℝ) := Nat.cast_nonneg _
  have hm : 1 ≤ (k:ℝ)+2 := by linarith
  have hlinear := coordinate_linear_budget (by linarith) hω hω1 hL hm hsmall
  have husmall : u*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 :=
    (mul_le_mul_of_nonneg_right huL (by positivity)).trans hsmall
  have hroot := coordinate_root_budget (by linarith) hω hu hKn hK (by positivity) husmall
  have hlog0 : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hlogK : Real.log ((K:ℝ)+1) ≤ Real.log (b+1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogk : Real.log ((k:ℝ)+1) ≤ k := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (show 0 < (k:ℝ)+1 by positivity)
  have hprefactor : Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1) ≤
      ((k:ℝ)+2)^2*(1+Real.log (b+1)) := by
    have hp := mul_le_mul_of_nonneg_left hlogK hk
    have hkm : (k:ℝ) ≤ ((k:ℝ)+2)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hkm hlog0]
  have hlog20 : 0 ≤ Real.log (20*b)+8 := by
    have ht : 0 ≤ Real.log (20*b) := Real.log_nonneg (by nlinarith)
    linarith
  have hfirst : (b+6-K)*(k:ℝ)^2 ≤ (Real.log (20*b)+8)*((k:ℝ)+2)^2 := by
    have ha : b+6-K ≤ Real.log (20*b)+8 := by linarith
    have hs : (k:ℝ)^2 ≤ ((k:ℝ)+2)^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right ha (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hs hlog20)
  have hLterm : L*(k:ℝ)^2 ≤ L*((k:ℝ)+2)^2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hL
  have huterm : ((k:ℝ)+2)^2*u ≤ L*((k:ℝ)+2)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right huL (sq_nonneg ((k:ℝ)+2))]
  nlinarith only [hprefactor,hfirst,hLterm,huterm,hlinear,hroot,hbudget]

end TotientAsymptotic

end

end OAI
