import Mathlib

namespace OAI


                                               
section

namespace MaximalSeshadri.NefNumerics
noncomputable section

lemma exists_homogeneous_surplus (H : ℤ) (r : ℕ) (a : ℝ)
    (hH : 0 < H) (hr : 0 < r) (ha : Real.sqrt ((H:ℝ)/r) < a) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧
      (r*m^2:ℕ) < (k:ℤ)^2*H ∧ (k:ℝ)*H < a*r*m := by
  let w := Real.sqrt ((H:ℝ)/r)
  have hHr : 0 < (H:ℝ) := by exact_mod_cast hH
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hHr hrr)
  have ha0 : 0 < a := hw.trans ha
  have har : 0 < a*r := mul_pos ha0 hrr
  have heq : (H:ℝ) = r*w^2 := by
    dsimp [w]
    rw [Real.sq_sqrt (div_nonneg hHr.le hrr.le)]
    field_simp
  have hlt : (H:ℝ)/(a*r) < w := by
    rw [div_lt_iff₀ har,heq]
    have hh := mul_lt_mul_of_pos_left ha (mul_pos hrr hw)
    nlinarith only [hh]
  obtain ⟨s,hs,hsw⟩ := exists_rat_btwn hlt
  have hs0 : 0 < (s:ℝ) := (div_pos hHr har).trans hs
  have hsQ : 0 < s := by exact_mod_cast hs0
  let k := s.den
  let m := s.num.toNat
  have hk : 0 < k := s.den_pos
  have hm : 0 < m := by have hh := Rat.num_pos.mpr hsQ; dsimp [m]; omega
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have em : (m:ℝ) = (k:ℝ)*(s:ℝ) := by
    dsimp [k,m]
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (Rat.num_pos.mpr hsQ).le,Rat.cast_def]
    have hd : (s.den:ℝ) ≠ 0 := by exact_mod_cast s.den_ne_zero
    field_simp
  refine ⟨k,m,hk,hm,?_,?_⟩
  · have hsq : (s:ℝ)^2 < w^2 := by nlinarith only [hs0,hw,hsw]
    have hmul := mul_lt_mul_of_pos_left hsq hrr
    have hh := mul_lt_mul_of_pos_left hmul (sq_pos_of_pos hkR)
    have hh' : (r:ℝ)*(m:ℝ)^2 < (k:ℝ)^2*H := by
      rw [em,heq]
      nlinarith only [hh]
    exact_mod_cast hh'
  · have hh := (div_lt_iff₀ har).mp hs
    have hmul := mul_lt_mul_of_pos_left hh hkR
    rw [em]
    nlinarith only [hmul]

end
end MaximalSeshadri.NefNumerics

end



end OAI
