import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeLSeriesBounds
import OAI.NumberTheory.JointDickman.Analysis.RieszDenominatorBounds

namespace OAI

/-! # Decay of the original Perron integrand on the right-hand line -/
namespace JointDickman
open Complex

noncomputable def squarefreeNormalizedPerron (z L : ℝ) (w : ℂ) : ℂ :=
  LSeries (fun n => (squarefreeWeight z n:ℂ)) (1+w) * exp ((L:ℂ)*w) / ((1+w)*(2+w))

theorem squarefreeNormalizedPerron_norm (z L : ℝ) (w : ℂ) :
    ‖squarefreeNormalizedPerron z L w‖ =
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) (1+w)‖ * Real.exp (L*w.re) /
        (‖1+w‖*‖2+w‖) := by
  simp only [squarefreeNormalizedPerron,norm_div,norm_mul,Complex.norm_exp,
    mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]

theorem squarefreeNormalizedPerron_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (w : ℂ), 0 < w.re → w.re ≤ 1 → 3 < |w.im| →
      ‖squarefreeNormalizedPerron z L w‖ ≤
        C*Real.exp (L*w.re)*|w.im|^(-3/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := squarefreeLSeries_high_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro L w hw hw1 ht
  have ht0 : 0 < |w.im| := by linarith
  have hs := hb (1+w) (by simpa using hw) (by simp only [add_re,one_re]; linarith) (by simpa using ht)
  simp only [add_im,one_im,zero_add] at hs
  have hd : |w.im|^2 ≤ ‖1+w‖*‖2+w‖ := by
    simpa only [add_im,one_im,zero_add,sq_abs,
      show (1:ℂ)+w+1 = 2+w by ring] using rieszDenominator_im_lower_bound (1+w)
  have hp : |w.im|^(1/2:ℝ)/|w.im|^2 = |w.im|^(-3/2:ℝ) := by
    rw [←Real.rpow_ofNat,←Real.rpow_sub ht0]
    norm_num
  rw [squarefreeNormalizedPerron_norm]
  calc
    _ ≤ (C*|w.im|^(1/2:ℝ)*Real.exp (L*w.re))/|w.im|^2 := by
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) (pow_pos ht0 2) hd
    _ = C*Real.exp (L*w.re)*(|w.im|^(1/2:ℝ)/|w.im|^2) := by ring
    _ = _ := by rw [hp]

end JointDickman

end OAI
