import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcQuotientScale

namespace OAI

/-! The actual nested correction, prefix and gcd quotients. No
identification of a rounded quotient with a real quotient is used. -/

namespace TwoPointCorrelations

lemma mrt_div_add_one_lower (n d : ℕ) (hd : 0 < d) :
    (n:ℝ)/d ≤ (n/d+1:ℕ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  apply le_of_lt
  apply (div_lt_iff₀ hdr).mpr
  have hh : (n:ℝ) < (d:ℝ)*(n/d+1:ℕ) := by
    exact_mod_cast Nat.lt_mul_div_succ n hd
  simpa only [mul_comm] using hh

lemma mrt_nested_outer_lower (V d b : ℕ) (hd : 0 < d) (hb : 0 < b) :
    (V:ℝ)/(d*b:ℕ) ≤ ((V/d+1)/b+1:ℕ) := by
  have hbr : (0:ℝ) < b := by exact_mod_cast hb
  calc
    (V:ℝ)/(d*b:ℕ) = ((V:ℝ)/d)/b := by push_cast; rw [div_div]
    _ ≤ ((V/d+1:ℕ):ℝ)/b :=
      div_le_div_of_nonneg_right (mrt_div_add_one_lower V d hd) hbr.le
    _ ≤ _ := mrt_div_add_one_lower (V/d+1) b hb

lemma mrt_nested_prefix_lower {W H : ℝ} {h k d b : ℕ}
    (hW : 0 < W) (hd : 0 < d) (hb : 0 < b)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    H/(W^4*(d:ℝ)*(b:ℝ)) ≤ (k/b+1:ℕ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hbr : (0:ℝ) < b := by exact_mod_cast hb
  have hfirst : (H/W^2)/(d:ℝ) ≤ (h/d+1:ℕ) :=
    (div_le_div_of_nonneg_right hh hdr.le).trans (mrt_div_add_one_lower h d hd)
  have hsecond : ((H/W^2)/(d:ℝ))/W^2 ≤ (k:ℝ) :=
    (div_le_div_of_nonneg_right hfirst (pow_nonneg hW.le _)).trans hk
  have hthird := (div_le_div_of_nonneg_right hsecond hbr.le).trans
    (mrt_div_add_one_lower k b hb)
  calc
    H/(W^4*(d:ℝ)*(b:ℝ)) = (((H/W^2)/(d:ℝ))/W^2)/(b:ℝ) := by
      simp only [div_div]
      congr 1
      ring
    _ ≤ _ := hthird

lemma mrt_nested_prefix_power_lower {W H : ℝ} {h k d b : ℕ}
    (hW : 0 < W) (hH : 0 ≤ H) (hd : 0 < d) (hb : 0 < b)
    (hdW : (d:ℝ) ≤ W^5) (hbW : (b:ℝ) ≤ W)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    H/W^10 ≤ (k/b+1:ℕ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hbr : (0:ℝ) < b := by exact_mod_cast hb
  have hdb := mrt_arc_combined_divisor hW.le hdW hbW
  have hden : W^4*(d:ℝ)*(b:ℝ) ≤ W^10 := by
    calc
      _ = W^4*((d*b:ℕ):ℝ) := by push_cast; ring
      _ ≤ W^4*W^6 := mul_le_mul_of_nonneg_left hdb (pow_nonneg hW.le _)
      _ = _ := by ring
  exact (div_le_div_of_nonneg_left hH (by positivity) hden).trans
    (mrt_nested_prefix_lower hW hd hb hh hk)

lemma mrt_nested_prefix_large {W H : ℝ} {h k d b : ℕ}
    (hW : 1 ≤ W) (hH : W^250 ≤ H) (hd : 0 < d) (hb : 0 < b)
    (hdW : (d:ℝ) ≤ W^5) (hbW : (b:ℝ) ≤ W)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    W^240 ≤ (k/b+1:ℕ) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 ≤ H := (pow_nonneg hW0.le 250).trans hH
  calc
    W^240 = W^250/W^10 := by
      rw [show (250:ℕ)=240+10 by decide,pow_add]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
    _ ≤ H/W^10 := div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)
    _ ≤ _ := mrt_nested_prefix_power_lower hW0 hH0 hd hb hdW hbW hh hk

lemma mrt_nested_prefix_prime_ratio {W H Q : ℝ} {h k d b : ℕ}
    (hW : 0 < W) (hH : 0 ≤ H) (hQ : Q ≤ H/W^3)
    (hd : 0 < d) (hb : 0 < b) (hdW : (d:ℝ) ≤ W^5) (hbW : (b:ℝ) ≤ W)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    Q/(k/b+1:ℕ) ≤ W^7 := by
  have hlen := mrt_nested_prefix_power_lower hW hH hd hb hdW hbW hh hk
  have hlen0 : (0:ℝ) < (k/b+1:ℕ) := by positivity
  apply (div_le_iff₀ hlen0).mpr
  calc
    Q ≤ H/W^3 := hQ
    _ = W^7*(H/W^10) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlen (pow_nonneg hW.le _)

lemma mrt_nested_prefix_upper {H h k d b : ℕ}
    (hh : h ≤ H) (hk : k ≤ h/d+1) : k/b+1 ≤ H+2 := by
  have hb := Nat.div_le_self k b
  have hd := Nat.div_le_self h d
  omega

end TwoPointCorrelations

end OAI
