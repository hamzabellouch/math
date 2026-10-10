import OAI.NumberTheory.JointDickman.Analysis.CharacterContourShift
import OAI.NumberTheory.JointDickman.Analysis.CharacterContourEdges
import OAI.NumberTheory.JointDickman.Analysis.CharacterPerronTruncation

namespace OAI

/-! # Combining the character contour errors -/
namespace JointDickman
open Complex Set

theorem characterPerron_contour_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ L δ c T B : ℝ, 0 ≤ L → 0 < δ → δ ≤ 1/4 → 0 < c → c ≤ 1/2 → 3 < T → 0 ≤ B →
      ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)) →
      f (3/2) = primeCharacterLog χ (3/2) →
      (∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = χ.LFunction s) →
      (∀ t ∈ Icc (-T) T,
        ‖characterContourSeries χ z f (1+(((-δ/2:ℝ):ℂ)+(t:ℂ)*I))‖ ≤ B) →
      (∀ u ∈ Icc (-δ/2) c,
        ‖characterContourSeries χ z f (1+((u:ℂ)+(T:ℂ)*I))‖ ≤ B) →
      (∀ u ∈ Icc (-δ/2) c,
        ‖characterContourSeries χ z f (1+((u:ℂ)-(T:ℂ)*I))‖ ≤ B) →
      ‖VerticalIntegral' (characterNormalizedPerron χ z L) c‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) +
        (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
          2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c))) := by
  obtain ⟨C,hC,htr⟩ := characterNormalizedPerron_truncation_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro q _ χ hn L δ c T B hL hδ hδ4 hc hc1 hT hB f hf hf0 he hl hu hd
  have hleft := characterRieszKernel_left_bound χ (z := z) (f := f) (L := L) (δ := δ/2) (T := T) (B := B)
    (by linarith) (by linarith) hB (by simpa only [neg_div] using hl)
  have hup := characterRieszKernel_horizontal_bound χ (z := z) (f := f) (L := L) (δ := δ/2) (T := T) (B := B)
    (ε := 1) (by linarith) (by linarith) hc.le hL hB (by norm_num)
    (by simpa only [one_mul, neg_div] using hu)
  have hdown := characterRieszKernel_horizontal_bound χ (z := z) (f := f) (L := L) (δ := δ/2) (T := T) (B := B)
    (ε := -1) (by linarith) (by linarith) hc.le hL hB (by norm_num)
    (by simpa only [neg_one_mul, one_mul, ofReal_neg, neg_mul, ←sub_eq_add_neg, neg_div] using hd)
  have hs := characterNormalizedPerron_finite_shift χ (L := L) hz hz1 hδ hδ4 hc hc1 (by linarith) hf hf0 he
  have hnorm : ‖(1/(2*(Real.pi:ℂ)*I))*VIntegral (characterNormalizedPerron χ z L) c (-T) T‖ ≤
      (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
        2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c))) := by
    rw [hs, norm_mul, perron_normalization_norm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := (norm_sub_le
      (VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T +
        HIntegral (characterRieszKernel χ z L f) (-δ/2) c T)
      (HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    have hp : ‖HIntegral (characterRieszKernel χ z L f) (-δ/2) c T‖ ≤
        (5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c) := by simpa only [one_mul, neg_div] using hup
    have hm : ‖HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T)‖ ≤
        (5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c) := by simpa only [neg_one_mul, neg_div] using hdown
    have hj : ‖VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T‖ ≤
        (5*B*Real.exp (-(L*(δ/2))))*Real.pi := by simpa only [neg_div] using hleft
    linarith
  have htriangle := norm_add_le
    (VerticalIntegral' (characterNormalizedPerron χ z L) c -
      (1/(2*(Real.pi:ℂ)*I))*VIntegral (characterNormalizedPerron χ z L) c (-T) T)
    ((1/(2*(Real.pi:ℂ)*I))*VIntegral (characterNormalizedPerron χ z L) c (-T) T)
  rw [sub_add_cancel] at htriangle
  exact htriangle.trans (add_le_add (htr q χ hn L c T hc (by linarith) hT) hnorm)

end JointDickman

end OAI
