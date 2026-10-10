import OAI.MeasureTheory.Falconer.Angular.GnomonicPairGram
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # The affine displacement angle controls the spherical triple determinant -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

noncomputable def displacementAngle (p q r : Space n) : ℝ :=
  ‖perpendicularPart (normalize (q-p)) (normalize (r-p))‖

theorem displacementAngle_nonneg (p q r : Space n) : 0 ≤ displacementAngle p q r :=
  norm_nonneg _

theorem displacement_pairGram (p q r : Space n) (hq : q ≠ p) (hr : r ≠ p) :
    pairGram (q-p) (r-p) = (‖q-p‖*‖r-p‖*displacementAngle p q r)^2 := by
  have hq0 : q-p ≠ 0 := sub_ne_zero.mpr hq
  have hr0 : r-p ≠ 0 := sub_ne_zero.mpr hr
  have hnq := norm_normalize hq0
  have hnr := norm_normalize hr0
  have hh := norm_perpendicularPart_sq hnq (normalize (r-p))
  rw [hnr] at hh
  have hg : pairGram (normalize (q-p)) (normalize (r-p)) =
      (displacementAngle p q r)^2 := by
    simp only [pairGram,hnq,hnr,one_pow,one_mul]
    simpa only [one_pow,displacementAngle] using hh.symm
  rw [NormedSpace.normalize,NormedSpace.normalize,pairGram_smul] at hg
  have hqn : ‖q-p‖ ≠ 0 := norm_ne_zero_iff.mpr hq0
  have hrn : ‖r-p‖ ≠ 0 := norm_ne_zero_iff.mpr hr0
  field_simp at hg
  nlinarith [sq_nonneg (displacementAngle p q r)]

theorem gnomonic_triple_sqrt_lower {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (hpq : q ≠ p) (hpr : r ≠ p) :
    ‖q-p‖*‖r-p‖*displacementAngle p q r/8 ≤
      Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
        (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))) := by
  have hh := gnomonic_tripleGram_lower hp hq hr
  change (1/64:ℝ)*pairGram (q-p) (r-p) ≤ _ at hh
  rw [displacement_pairGram p q r hpq hpr] at hh
  have hs := Real.sq_sqrt (tripleGram_nonnegative
    (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
    (gnomonicChart r : Space (n+1)))
  nlinarith [Real.sqrt_nonneg (tripleGram (gnomonicChart p : Space (n+1))
    (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))),
    mul_nonneg (mul_nonneg (norm_nonneg (q-p)) (norm_nonneg (r-p)))
      (displacementAngle_nonneg p q r)]

theorem displacementAngle_lt_of_tripleGram {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    {b W : ℝ} (hb : 0 < b) (hpq : b ≤ ‖q-p‖) (hpr : b ≤ ‖r-p‖)
    (hsmall : Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))) < W) :
    displacementAngle p q r < 8*W/b^2 := by
  have hqne : q ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpq
    linarith
  have hrne : r ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpr
    linarith
  have hh := (gnomonic_triple_sqrt_lower hp hq hr hqne hrne).trans_lt hsmall
  have hm : b^2*displacementAngle p q r ≤ ‖q-p‖*‖r-p‖*displacementAngle p q r := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hpq hpr hb.le (norm_nonneg _))
      (displacementAngle_nonneg p q r)
  apply (lt_div_iff₀ (sq_pos_of_pos hb)).mpr
  nlinarith

end Falconer

end OAI
