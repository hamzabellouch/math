import Mathlib
import OAI.NumberTheory.Jacobsthal.Probability.FirstHitKernels

namespace OAI

namespace Erdos970

section

namespace ErdosEvenThreshold
open Set NumberTheoryLean.FinitePathGeometry

noncomputable def thresholdSlack (R t : ℝ) : ℝ :=
  nextGap R t-max (2*nextExponent R t) (nextExponent R t+2)
noncomputable def thresholdStrip (R d : ℝ) : Set ℝ :=
  {t | 2 ≤ t ∧ 1 < nextExponent R t ∧ 0 ≤ thresholdSlack R t ∧ thresholdSlack R t ≤ d}

theorem gap_eq_exponent_mul (R t : ℝ) : nextGap R t=nextExponent R t*t := by
  unfold nextGap nextExponent
  ring

theorem exponent_mul_add_one {R t : ℝ} (ht : 0 < t+1) : nextExponent R t*(t+1)=R := by
  unfold nextExponent
  field_simp

theorem strip_parameters {R d t : ℝ} (hd : d ≤ 1) (ht : t ∈ thresholdStrip R d) :
    4 < R ∧ t ≤ 4 := by
  obtain ⟨ht2,hx,hlo,hhi⟩ := ht
  have hcons := gap_exponent_conservation (r:=R) (show 0 < t by linarith)
  have hm := gap_eq_exponent_mul R t
  have hlow := le_max_right (2*nextExponent R t) (nextExponent R t+2)
  have hmax : max (2*nextExponent R t) (nextExponent R t+2) ≤ 3*nextExponent R t :=
    max_le (by linarith) (by linarith)
  unfold thresholdSlack at hlo hhi
  constructor
  · linarith
  · have hprod : nextExponent R t*t ≤ nextExponent R t*4 := by nlinarith
    exact le_of_mul_le_mul_left hprod (by linarith : 0 < nextExponent R t)

noncomputable def firstUpper (R d : ℝ) : ℝ := 2+4*d/R
noncomputable def secondLower (R : ℝ) : ℝ := (R+2)/(R-2)
noncomputable def secondUpper (R d : ℝ) : ℝ := (R+2+d)/(R-2-d)

theorem strip_mem_cover {R d t : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (ht : t ∈ thresholdStrip R d) :
    t ∈ Icc 2 (firstUpper R d) ∪ Icc (secondLower R) (secondUpper R d) := by
  have hR := (strip_parameters hd1 ht).1
  have hR0 : 0 < R := by linarith
  obtain ⟨ht2,hx,hlo,hhi⟩ := ht
  have htpos : 0 < t+1 := by linarith
  have hxpos : 0 < nextExponent R t := by linarith
  have hm := gap_eq_exponent_mul R t
  have hxR := exponent_mul_add_one (R:=R) htpos
  unfold thresholdSlack at hlo hhi
  by_cases hb : nextExponent R t+2 ≤ 2*nextExponent R t
  · rw [max_eq_left hb] at hlo hhi
    have hs : nextExponent R t*(t-2) ≤ d := by nlinarith
    have ht3 : t ≤ 3 := by
      have hh : nextExponent R t*t ≤ nextExponent R t*3 := by nlinarith
      exact le_of_mul_le_mul_left hh hxpos
    have hbound : t-2 ≤ 4*d/R := by
      apply (le_div_iff₀ hR0).mpr
      calc
        (t-2)*R=(nextExponent R t*(t-2))*(t+1) := by
          conv_lhs => rw [← hxR]
          ring
        _ ≤ d*(t+1) := mul_le_mul_of_nonneg_right hs htpos.le
        _ ≤ d*4 := mul_le_mul_of_nonneg_left (by linarith : t+1 ≤ 4) hd0
        _ = _ := by ring
    exact Or.inl ⟨ht2,by unfold firstUpper; linarith⟩
  · have hb' : 2*nextExponent R t ≤ nextExponent R t+2 := (lt_of_not_ge hb).le
    rw [max_eq_right hb'] at hlo hhi
    have he : (nextGap R t-nextExponent R t)*(t+1)=R*(t-1) := by
      rw [hm]
      calc
        _ = (nextExponent R t*(t+1))*(t-1) := by ring
        _ = _ := by rw [hxR]
    have hlow : 2*(t+1) ≤ (nextGap R t-nextExponent R t)*(t+1) :=
      mul_le_mul_of_nonneg_right (by linarith) htpos.le
    have hhigh : (nextGap R t-nextExponent R t)*(t+1) ≤ (2+d)*(t+1) :=
      mul_le_mul_of_nonneg_right (by linarith) htpos.le
    rw [he] at hlow hhigh
    apply Or.inr
    constructor
    · apply (div_le_iff₀ (show 0 < R-2 by linarith)).mpr
      nlinarith
    · apply (le_div_iff₀ (show 0 < R-2-d by linarith)).mpr
      nlinarith

end ErdosEvenThreshold

end

end Erdos970

end OAI
