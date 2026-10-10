import OAI.NumberTheory.JointDickman.Analysis.CharacterContourBounds
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterPerron
import OAI.NumberTheory.JointDickman.Analysis.RieszContourBounds

namespace OAI

/-! # The regular character Riesz kernel and its vertical bound -/
namespace JointDickman
open Complex Set MeasureTheory

noncomputable def characterNormalizedPerron {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (w : ℂ) : ℂ :=
  LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (1+w) *
    exp ((L:ℂ)*w) / ((1+w)*(2+w))

noncomputable def characterRieszKernel {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  characterContourSeries χ z f (1+w) * exp ((L:ℂ)*w) / ((1+w)*(2+w))

theorem characterRieszKernel_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (f : ℂ → ℂ) (w : ℂ) :
    ‖characterRieszKernel χ z L f w‖ =
      ‖characterContourSeries χ z f (1+w)‖ * Real.exp (L*w.re) / (‖1+w‖*‖2+w‖) := by
  simp only [characterRieszKernel, norm_div, norm_mul, Complex.norm_exp,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

theorem characterNormalizedPerron_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (w : ℂ) :
    (Real.exp L:ℂ)*characterNormalizedPerron χ z L w =
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (1+w) *
        Perron.f (Real.exp L) (1+w) := by
  have he : ((Real.exp L:ℝ):ℂ)^(1+w) = (Real.exp L:ℂ)*exp ((L:ℂ)*w) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
      ←Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp, mul_add, mul_one,
      Complex.exp_add, ←Complex.ofReal_exp]
  rw [characterNormalizedPerron, Perron.f, he]
  rw [show (1:ℂ)+w+1 = 2+w by ring]
  ring

theorem characterNormalizedPerron_riesz {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L c : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 < c) :
    (Real.exp L:ℂ)*VerticalIntegral' (characterNormalizedPerron χ z L) c =
      squarefreeCharacterRieszSum χ z (Real.exp L) := by
  have hp := squarefreeCharacter_perron_riesz χ hz hz1 (Real.exp_pos L)
    (show 1 < 1+c by linarith)
  rw [←hp]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  have heq : (fun t : ℝ => (Real.exp L:ℂ)*
      characterNormalizedPerron χ z L ((c:ℂ)+(t:ℂ)*I)) =
    (fun t : ℝ => LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
      (((1+c:ℝ):ℂ)+(t:ℂ)*I) * Perron.f (Real.exp L) (((1+c:ℝ):ℂ)+(t:ℂ)*I)) := by
    funext t
    rw [characterNormalizedPerron_eq]
    congr 2 <;> push_cast <;> ring
  rw [←heq, integral_const_mul]
  ring

theorem characterRieszKernel_point_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L B : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hB : 0 ≤ B) (hs : 1/2 ≤ (1+w).re)
    (hb : ‖characterContourSeries χ z f (1+w)‖ ≤ B) :
    ‖characterRieszKernel χ z L f w‖ ≤ 5*B*Real.exp (L*w.re)/(1+w.im^2) := by
  have hd : 1/(‖1+w‖*‖2+w‖) ≤ 5/(1+w.im^2) := by
    simpa only [add_im, one_im, zero_add, show (1:ℂ)+w+1 = 2+w by ring] using
      rieszDenominator_inv_bound hs
  rw [characterRieszKernel_norm]
  calc
    _ = (‖characterContourSeries χ z f (1+w)‖*Real.exp (L*w.re)) *
        (1/(‖1+w‖*‖2+w‖)) := by ring
    _ ≤ (B*Real.exp (L*w.re))*(5/(1+w.im^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le) hd
        (by positivity) (by positivity)
    _ = _ := by ring

theorem characterRieszKernel_left_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L δ T B : ℝ} {f : ℂ → ℂ}
    (hδ : δ ≤ 1/2) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Icc (-T) T,
      ‖characterContourSeries χ z f (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I))‖ ≤ B) :
    ‖VIntegral (characterRieszKernel χ z L f) (-δ) (-T) T‖ ≤
      (5*B*Real.exp (-(L*δ)))*Real.pi := by
  apply verticalIntegral_bound_by_cauchy hT (by positivity)
  intro t ht
  have hs : 1/2 ≤ (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I)).re := by simp; linarith
  have he := characterRieszKernel_point_bound χ (L := L) hB hs (hb t ⟨ht.1.le,ht.2⟩)
  simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add, mul_neg] using he

end JointDickman

end OAI
