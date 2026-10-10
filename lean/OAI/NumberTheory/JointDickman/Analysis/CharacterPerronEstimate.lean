import OAI.NumberTheory.JointDickman.Analysis.CharacterContourEstimate
import OAI.NumberTheory.JointDickman.Analysis.CharacterRectangleBound

namespace OAI

/-! # An unconditional quantitative bound for the actual character Perron integral -/
namespace JointDickman
open Complex Set

theorem characterPerron_estimate {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A C K : ℝ, 0 < A ∧ A ≤ 1/4 ∧ 0 < C ∧ 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ L c T : ℝ, 0 ≤ L → 0 < c → c ≤ 1/2 → 3 < T →
      let δ := characterContourWidth A ε q (2*T)
      let B := K*(((q:ℝ)+2)*(T+2))^(1/4:ℝ)
      ‖VerticalIntegral' (characterNormalizedPerron χ z L) c‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) +
        (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
          2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c))) := by
  obtain ⟨A,hA,hA4,hlog⟩ := character_rectangle_log hε hε1
  obtain ⟨C,hC,hest⟩ := characterPerron_contour_bound hz hz1
  obtain ⟨K,hK,hbounds⟩ := characterContourSeries_closed_rectangle_bound hz hz1
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 1/4)
  refine ⟨A,C,K,hA,hA4,hC,hK,?_⟩
  intro q _ χ hn L c T hL hc hc1 hT
  let δ := characterContourWidth A ε q (2*T)
  let B := K*(((q:ℝ)+2)*(T+2))^(1/4:ℝ)
  have hδ : 0 < δ := by
    dsimp [δ, characterContourWidth]
    exact mul_pos hA (Real.rpow_pos_of_pos (by positivity) _)
  have hδ4 : δ ≤ 1/4 := by
    have hw : 1 ≤ ((q:ℝ)+2)*(2*T+2) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hw (show -ε ≤ 0 by linarith)
    exact (mul_le_of_le_one_right hA.le hp).trans hA4
  obtain ⟨f,hf,hf0,he⟩ := hlog q χ hn (2*T) (by linarith)
    (primeCharacterLog χ (3/2)) (primeCharacterLog_exp χ (by norm_num))
  have hb (w : ℂ) (hw : -δ/2 ≤ w.re) (hwc : w.re ≤ c) (hwi : |w.im| ≤ T) :
      ‖characterContourSeries χ z f (1+w)‖ ≤ B :=
    hbounds q χ hn δ c T hδ hδ4 hc1 (by linarith) f he w hw hwc hwi
  apply hest q χ hn L δ c T B hL hδ hδ4 hc hc1 hT (by dsimp [B]; positivity) f hf hf0 he
  · intro t ht
    apply hb
    · simp
    · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_zero, add_zero]
      linarith
    · simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
        mul_one, zero_add, add_zero] using abs_le.mpr ht
  · intro u hu
    apply hb
    · simpa using hu.1
    · simpa using hu.2
    · simp [abs_of_pos (show 0 < T by linarith)]
  · intro u hu
    have hw : |((u:ℂ)-(T:ℂ)*I).im| ≤ T := by
      simp [abs_of_pos (show 0 < T by linarith)]
    have hh := hb ((u:ℂ)-(T:ℂ)*I) (by simpa using hu.1) (by simpa using hu.2) hw
    simpa only [sub_eq_add_neg] using hh

end JointDickman

end OAI
