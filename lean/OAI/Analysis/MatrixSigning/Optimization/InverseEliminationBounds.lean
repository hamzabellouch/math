import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Variables

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.KKT
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inverse_elimination_bounds (e : E) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (z rhs : Variables E) (hz : jacobian e L.toContinuousLinearMap H z = rhs)
    {b H0 δ : ℝ} (hb : 0 ≤ b) (hH0 : 0 ≤ H0) (hδ : 0 < δ)
    (hB : ‖L.symm.toContinuousLinearMap‖ ≤ b) (hBe : ‖L.symm e‖ ≤ b)
    (hH : ‖H‖ ≤ H0) (hden : δ ≤ inner ℝ (L.symm e) (H (L.symm e))) (hrhs : ‖rhs‖ ≤ 1) :
    |z.1| ≤ (1+b+H0*b^2)/δ ∧
    ‖z.2.1‖ ≤ b*(1+|z.1|) ∧
    ‖z.2.2‖ ≤ b*(1+H0*‖z.2.1‖) := by
  have hr : |rhs.1| ≤ 1 := by
    exact (norm_fst_le rhs).trans hrhs
  have hf : ‖rhs.2.1‖ ≤ 1 := (norm_fst_le rhs.2).trans ((norm_snd_le rhs).trans hrhs)
  have hg : ‖rhs.2.2‖ ≤ 1 := (norm_snd_le rhs.2).trans ((norm_snd_le rhs).trans hrhs)
  have hbn (x : E) : ‖L.symm x‖ ≤ b*‖x‖ :=
    (L.symm.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hhn (x : E) : ‖H x‖ ≤ H0*‖x‖ :=
    (H.le_opNorm x).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  obtain ⟨hu,_hp,hh⟩ := inverse_elimination e L hL H z rhs hz
  have hscalar : |z.1| ≤ (1+b+H0*b^2)/δ := by
    have hnum : |inner ℝ (L.symm e) rhs.2.2 + inner ℝ (L.symm e) (H (L.symm rhs.2.1)) - rhs.1| ≤
        b+H0*b^2+1 := by
      calc
        _ ≤ |inner ℝ (L.symm e) rhs.2.2|+|inner ℝ (L.symm e) (H (L.symm rhs.2.1))|+|rhs.1| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
        _ ≤ ‖L.symm e‖*‖rhs.2.2‖+‖L.symm e‖*‖H (L.symm rhs.2.1)‖+1 := by
          gcongr <;> exact abs_real_inner_le_norm _ _
        _ ≤ b*1+b*(H0*(b*1))+1 := by
          have hnorm : ‖H (L.symm rhs.2.1)‖ ≤ H0*(b*1) :=
            (hhn _).trans (mul_le_mul_of_nonneg_left
              ((hbn _).trans (mul_le_mul_of_nonneg_left hf hb)) hH0)
          exact add_le_add (add_le_add
            (mul_le_mul hBe hg (norm_nonneg _) hb)
            (mul_le_mul hBe hnorm (norm_nonneg _) hb)) (le_refl 1)
        _ = _ := by ring
    rw [← hh,abs_mul,abs_of_pos (hδ.trans_le hden)] at hnum
    have hm := mul_le_mul_of_nonneg_left hden (abs_nonneg z.1)
    exact (le_div_iff₀ hδ).mpr (by linarith)
  refine ⟨hscalar,?_,?_⟩
  · rw [hu]
    calc
      _ ≤ ‖L.symm rhs.2.1‖+‖z.1 • L.symm e‖ := norm_sub_le _ _
      _ ≤ b*1+|z.1| * b := by
        rw [norm_smul,Real.norm_eq_abs]
        exact add_le_add ((hbn _).trans (mul_le_mul_of_nonneg_left hf hb))
          (mul_le_mul_of_nonneg_left hBe (abs_nonneg _))
      _ = _ := by ring
  · have hg' : z.2.2 = L.symm (rhs.2.2+H z.2.1) := by
      apply L.injective
      rw [L.apply_symm_apply]
      have he := congrArg (fun w : Variables E => w.2.2) hz
      change L z.2.2-H z.2.1 = rhs.2.2 at he
      exact sub_eq_iff_eq_add.mp he
    rw [hg']
    calc
      _ ≤ b*‖rhs.2.2+H z.2.1‖ := hbn _
      _ ≤ b*(‖rhs.2.2‖+‖H z.2.1‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hb
      _ ≤ b*(1+H0*‖z.2.1‖) := mul_le_mul_of_nonneg_left (add_le_add hg (hhn _)) hb

lemma inverse_elimination_numeric {d b h u p : ℝ} (hd : 0 < d) (hb : 0 ≤ b)
    (hh : |h| ≤ (1+b+16000000*b^2)/(1/(100*d)))
    (hu : u ≤ b*(1+|h|)) (hp : p ≤ b*(1+16000000*u)) :
    |h| ≤ 10^18*(d+1)*(1+b)^4 ∧ u ≤ 10^18*(d+1)*(1+b)^4 ∧
      p ≤ 10^18*(d+1)*(1+b)^4 := by
  let s := 1+b
  have hs : 1 ≤ s := by dsimp [s]; linarith
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  have hbs : b ≤ s := by dsimp [s]; linarith
  have hD : 1 ≤ d+1 := by linarith
  have hD0 : 0 ≤ d+1 := by linarith
  have hs2 : 1 ≤ s^2 := one_le_pow₀ hs
  have hs3 : 1 ≤ s^3 := one_le_pow₀ hs
  have hs4 : 1 ≤ s^4 := one_le_pow₀ hs
  have hs12 : s ≤ s^2 := by nlinarith
  have hb2 : b^2 ≤ s^2 := pow_le_pow_left₀ hb hbs _
  have hD2 : 1 ≤ (d+1)*s^2 := one_le_mul_of_one_le_of_one_le hD hs2
  have hD3 : 1 ≤ (d+1)*s^3 := one_le_mul_of_one_le_of_one_le hD hs3
  have hsmall : |h| ≤ 2000000000*(d+1)*s^2 := by
    have hfrac : (1+b+16000000*b^2)/(1/(100*d)) = 100*d*(1+b+16000000*b^2) := by field_simp
    rw [hfrac] at hh
    calc
      _ ≤ 100*d*(1+b+16000000*b^2) := hh
      _ ≤ 100*d*(16000001*s^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [s] at hs12
        nlinarith
      _ ≤ 2000000000*(d+1)*s^2 := by nlinarith [mul_nonneg hd.le (sq_nonneg s)]
  have hu' : u ≤ 3000000000*(d+1)*s^3 := by
    calc
      _ ≤ b*(1+|h|) := hu
      _ ≤ s*(1+2000000000*(d+1)*s^2) := by gcongr
      _ ≤ s*(3000000000*(d+1)*s^2) := by
        apply mul_le_mul_of_nonneg_left _ hs0
        nlinarith
      _ = _ := by ring
  have hp' : p ≤ 50000000000000000*(d+1)*s^4 := by
    calc
      _ ≤ b*(1+16000000*u) := hp
      _ ≤ b*(1+16000000*(3000000000*(d+1)*s^3)) := by gcongr
      _ ≤ s*(1+16000000*(3000000000*(d+1)*s^3)) := by gcongr
      _ ≤ s*(50000000000000000*(d+1)*s^3) := by
        apply mul_le_mul_of_nonneg_left _ hs0
        nlinarith
      _ = _ := by ring
  have hs24 : s^2 ≤ s^4 := pow_le_pow_right₀ hs (by omega)
  have hs34 : s^3 ≤ s^4 := pow_le_pow_right₀ hs (by omega)
  change |h| ≤ (10:ℝ)^18*(d+1)*s^4 ∧ u ≤ (10:ℝ)^18*(d+1)*s^4 ∧
    p ≤ (10:ℝ)^18*(d+1)*s^4
  refine ⟨hsmall.trans ?_,hu'.trans ?_,hp'.trans ?_⟩
  · gcongr; norm_num
  · gcongr; norm_num
  · gcongr; norm_num

lemma jacobian_inverse_norm_100 (e : E) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (J : Variables E ≃L[ℝ] Variables E)
    (hJ : ∀ z,J z = jacobian e L.toContinuousLinearMap H z)
    {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hB : ‖L.symm.toContinuousLinearMap‖ ≤ ε⁻¹) (hBe : ‖L.symm e‖ ≤ ε⁻¹)
    (hH : ‖H‖ ≤ 16000000)
    (hden : 1/(100*d) ≤ inner ℝ (L.symm e) (H (L.symm e))) :
    ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*(d+1)*(1+ε⁻¹)^4 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro rhs hrhs
  have heq : jacobian e L.toContinuousLinearMap H (J.symm rhs) = rhs := by
    rw [← hJ,J.apply_symm_apply]
  obtain ⟨hh,hu,hp⟩ := inverse_elimination_bounds e L hL H _ rhs heq (inv_nonneg.mpr hε.le)
    (show (0:ℝ)≤16000000 by norm_num) (show 0<1/(100*d) by positivity) hB hBe hH hden hrhs.le
  obtain ⟨hh',hu',hp'⟩ := inverse_elimination_numeric hd (inv_nonneg.mpr hε.le) hh hu hp
  change max |(J.symm rhs).1| (max ‖(J.symm rhs).2.1‖ ‖(J.symm rhs).2.2‖) ≤ _
  exact max_le hh' (max_le hu' hp')

end CurrentKS.KKT

end

end OAI
