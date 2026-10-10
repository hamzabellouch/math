import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszKernel
import OAI.NumberTheory.JointDickman.Analysis.ZetaContourBounds
import OAI.NumberTheory.JointDickman.Analysis.RieszDenominatorBounds

namespace OAI

/-! # The horizontal errors in the squarefree Riesz contour -/
namespace JointDickman
open Complex Set

theorem squarefreeRieszKernel_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ A C : ℝ, A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
      ∀ (L : ℝ) (f : ℂ → ℂ) (w : ℂ), 3 < |w.im| →
        3/4 ≤ (1+w).re → (1+w).re ≤ 2 →
        1-A/Real.log |w.im| ≤ (1+w).re →
        exp (f (1+w)) = zetaPoleFactor (1+w) →
        ‖fractionalContourIntegrand z (squarefreeRieszKernel z L f) w‖ ≤
          C*Real.exp (L*w.re)*|w.im|^(-3/2:ℝ) := by
  obtain ⟨A,C,hA,hC,hζ⟩ := zeta_fractional_power_high_bound
  obtain ⟨G,hG,hGb⟩ := squarefreeAnalyticFactor_uniform_bound hz hz1 (by norm_num : (1/2:ℝ) < 3/4)
  refine ⟨A,G*C,hA,mul_pos hG hC,?_⟩
  intro L f w ht hs hs2 hsA hf
  have ht0 : 0 < |w.im| := by linarith
  have hw : w ≠ 0 := by
    intro hw
    simp only [hw,zero_im,abs_zero] at ht
    linarith
  have heq : (((1+w).re:ℝ):ℂ)+(w.im:ℂ)*I = 1+w := by
    apply Complex.ext <;> simp
  have hb := hζ z (1+w).re w.im hz hz1 ht ⟨hsA,hs2⟩
  rw [heq] at hb
  have hd : |w.im|^2 ≤ ‖1+w‖*‖2+w‖ := by
    simpa only [add_im,one_im,zero_add,sq_abs,
      show (1:ℂ)+w+1 = 2+w by ring] using rieszDenominator_im_lower_bound (1+w)
  have hp : |w.im|^(1/2:ℝ)/|w.im|^2 = |w.im|^(-3/2:ℝ) := by
    rw [←Real.rpow_ofNat,←Real.rpow_sub ht0]
    norm_num
  rw [squarefreeRieszKernel_norm hw hf]
  calc
    _ ≤ (G*(C*|w.im|^(1/2:ℝ))*Real.exp (L*w.re))/|w.im|^2 := by
      apply div_le_div₀ (by positivity) _ (pow_pos ht0 2) hd
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hGb (1+w) hs) hb (Real.rpow_nonneg (norm_nonneg _) _) hG.le)
        (Real.exp_pos _).le
    _ = (G*C)*Real.exp (L*w.re)*(|w.im|^(1/2:ℝ)/|w.im|^2) := by ring
    _ = _ := by rw [hp]

theorem squarefreeRiesz_horizontal_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ A C : ℝ, A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
      ∀ (δ c T L ε : ℝ) (f : ℂ → ℂ), 0 ≤ δ → δ ≤ 1/4 → 0 ≤ c → c ≤ 1 →
        3 < T → 0 ≤ L → δ ≤ A/Real.log T → |ε| = 1 →
        (∀ u ∈ Icc (-δ) c, exp (f (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I))) =
          zetaPoleFactor (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I))) →
        ‖HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f))
          (-δ) c (ε*T)‖ ≤ C*Real.exp (L*c)*T^(-3/2:ℝ)*(δ+c) := by
  obtain ⟨A,C,hA,hC,hb⟩ := squarefreeRieszKernel_high_bound hz hz1
  refine ⟨A,C,hA,hC,?_⟩
  intro δ c T L ε f hδ hδ4 hc hc1 hT hL hδA hε hf
  have hT0 : 0 < T := by linarith
  have hac : -δ ≤ c := by linarith
  unfold HIntegral
  have hbound : ‖∫ u in -δ..c,
      fractionalContourIntegrand z (squarefreeRieszKernel z L f)
        ((u:ℂ)+((ε*T:ℝ):ℂ)*I)‖ ≤
      (C*Real.exp (L*c)*T^(-3/2:ℝ))*|c-(-δ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    have hu' : -δ ≤ u ∧ u ≤ c := by
      have hh : u ∈ Ioc (-δ) c := by simpa only [uIoc_of_le hac] using hu
      exact ⟨hh.1.le,hh.2⟩
    have hi : |(((u:ℂ)+((ε*T:ℝ):ℂ)*I)).im| = T := by
      simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,
        zero_add,add_zero,abs_mul,hε,one_mul,abs_of_pos hT0]
    have hr : (((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re = u := by simp
    have hs : (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re = 1+u := by simp
    have ht := hb L f ((u:ℂ)+((ε*T:ℝ):ℂ)*I)
      (by rwa [hi]) (by rw [hs]; linarith) (by rw [hs]; linarith)
      (by rw [hi,hs]; linarith) (hf u hu')
    rw [hi,hr] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu'.2 hL)) hC.le)
      (Real.rpow_nonneg hT0.le _))
  rw [abs_of_nonneg (by linarith : 0 ≤ c-(-δ))] at hbound
  simpa only [sub_neg_eq_add,add_comm c δ] using hbound

end JointDickman

end OAI
