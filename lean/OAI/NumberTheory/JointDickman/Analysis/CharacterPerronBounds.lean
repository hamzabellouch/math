import OAI.NumberTheory.JointDickman.Analysis.CharacterRieszKernel

namespace OAI

/-! # Uniform decay on the original character Perron line -/
namespace JointDickman
open Complex

theorem characterLSeries_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 3 < |s.im| →
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*|s.im|^(1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := characterContourSeries_small_power hz hz1
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 1/4)
  refine ⟨C*3^(1/4:ℝ), by positivity, ?_⟩
  intro q _ χ hn s hs hs2 ht
  have ht0 : 0 < |s.im| := by linarith
  have hnS : ‖s‖+2 ≤ 3*|s.im| := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at hh
    linarith
  have hbase : ((q:ℝ)+2)*(‖s‖+2) ≤ 3*(((q:ℝ)+2)*|s.im|) := by
    nlinarith [mul_le_mul_of_nonneg_left hnS (show (0:ℝ) ≤ q+2 by positivity)]
  have hp : |s.im|^(1/4:ℝ) ≤ |s.im|^(1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h := hb q χ hn (primeCharacterLog χ) s (by linarith) (primeCharacterLog_exp χ hs)
  rw [characterContourSeries, ←squarefreeCharacterDirichletSeries_factorization χ hz hz1 hs] at h
  calc
    _ ≤ C*(((q:ℝ)+2)*(‖s‖+2))^(1/4:ℝ) := h
    _ ≤ C*(3*(((q:ℝ)+2)*|s.im|))^(1/4:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hbase (by norm_num)) hC.le
    _ = C*3^(1/4:ℝ)*((q:ℝ)+2)^(1/4:ℝ)*|s.im|^(1/4:ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity) ht0.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem characterNormalizedPerron_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (w : ℂ) :
    ‖characterNormalizedPerron χ z L w‖ =
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (1+w)‖ *
        Real.exp (L*w.re) / (‖1+w‖*‖2+w‖) := by
  simp only [characterNormalizedPerron, norm_div, norm_mul, Complex.norm_exp,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

theorem characterNormalizedPerron_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (L : ℝ) (w : ℂ), 0 < w.re → w.re ≤ 1 → 3 < |w.im| →
      ‖characterNormalizedPerron χ z L w‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*w.re)*|w.im|^(-3/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := characterLSeries_high_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro q _ χ hn L w hw hw1 ht
  have ht0 : 0 < |w.im| := by linarith
  have hs := hb q χ hn (1+w) (by simpa using hw)
    (by simp only [add_re, one_re]; linarith) (by simpa using ht)
  simp only [add_im, one_im, zero_add] at hs
  have hd : |w.im|^2 ≤ ‖1+w‖*‖2+w‖ := by
    simpa only [add_im, one_im, zero_add, sq_abs,
      show (1:ℂ)+w+1 = 2+w by ring] using rieszDenominator_im_lower_bound (1+w)
  have hp : |w.im|^(1/2:ℝ)/|w.im|^2 = |w.im|^(-3/2:ℝ) := by
    rw [←Real.rpow_ofNat, ←Real.rpow_sub ht0]
    norm_num
  rw [characterNormalizedPerron_norm]
  calc
    _ ≤ (C*((q:ℝ)+2)^(1/4:ℝ)*|w.im|^(1/2:ℝ)*Real.exp (L*w.re))/|w.im|^2 :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le)
        (pow_pos ht0 2) hd
    _ = C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*w.re)*
        (|w.im|^(1/2:ℝ)/|w.im|^2) := by ring
    _ = _ := by rw [hp]

end JointDickman

end OAI
