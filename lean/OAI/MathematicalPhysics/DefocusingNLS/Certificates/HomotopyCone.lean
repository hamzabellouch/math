import OAI.MathematicalPhysics.DefocusingNLS.Certificates.NormalizedTailHolomorphy
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardMatching

namespace OAI

/-! # The terminal cone along the tail homotopy -/

namespace DefocusingNLS

theorem coneForm_scale (M : ℝ) (s a B C : ℂ) :
    coneForm M s (a * B) (a * C) = Complex.normSq a * coneForm M s B C := by
  have he : s * star (a * B) * (a * C) =
      (Complex.normSq a : ℂ) * (s * star B * C) := by
    calc
      _ = (a * star a) * (s * star B * C) := by rw [star_mul]; ring
      _ = _ := by
        have ha : a * star a = (Complex.normSq a : ℂ) := by
          simpa only [starRingEnd_apply] using Complex.mul_conj a
        rw [ha]
  simp only [coneForm, Complex.normSq_mul, he, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem coneForm_ratio (M : ℝ) (s B C : ℂ) (hC : C ≠ 0) :
    coneForm M s (B / C) 1 = Complex.normSq C⁻¹ * coneForm M s B C := by
  have h := coneForm_scale M s C⁻¹ B C
  simpa only [inv_mul_cancel₀ hC, div_eq_mul_inv, mul_comm C⁻¹ B] using h

theorem coneForm_real_contraction (M : ℝ) (s R : ℂ) (ρ : ℝ) :
    coneForm M s ((ρ : ℂ) * R) 1 =
      ρ * coneForm M s R 1 - M / 2 * ρ * (1 - ρ) * Complex.normSq R := by
  simp only [coneForm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

theorem coneForm_nonpos_of_contraction (M : ℝ) (s R : ℂ) (ρ : ℝ)
    (hM : 0 ≤ M) (hR : coneForm M s R 1 < 0) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    coneForm M s ((ρ : ℂ) * R) 1 ≤ 0 := by
  rw [coneForm_real_contraction]
  have h₁ : ρ * coneForm M s R 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ hR.le
  have h₂ : 0 ≤ M / 2 * ρ * (1 - ρ) * Complex.normSq R :=
    mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hM (by norm_num)) hρ)
      (by linarith)) (Complex.normSq_nonneg R)
  linarith

theorem slowTailRatio_strict_cone (σ : ℝ) (ℓ K : ℕ) (q s : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    coneForm ((ℓ : ℝ) + 5) s (slowTailRatio q (ℓ + 6) K s) 1 < 0 := by
  have h := normalizedSlow_strict_cone σ ℓ K q s hσ hK hq hsre hsim
  have hC := (normalizedSlow_tail_disk σ ℓ K q s hσ hK hq hsre hsim).1
  have hq' : -1 < q.re := by rw [hq]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hp := shiftedPochhammer_ne_zero q (K - 1) hq'
  have hquot : slowTailRatio q (ℓ + 6) K s =
      normalizedSlowB q (ℓ + 6) s K / normalizedSlowC q (ℓ + 6) s K := by
    unfold slowTailRatio normalizedMatchingB normalizedMatchingC
    field_simp [hp]
  rw [hquot, coneForm_ratio _ _ _ _ hC]
  exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr (inv_ne_zero hC)) h

/-- Every terminal pair in the straight tail homotopy has nonpositive cone. -/
theorem slowTailRatio_homotopy_cone (σ : ℝ) (ℓ K : ℕ) (q s : ℂ) (ρ : ℝ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hsre : s.re = 0) (hsim : s.im ≠ 0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    coneForm ((ℓ : ℝ) + 5) s ((ρ : ℂ) * slowTailRatio q (ℓ + 6) K s) 1 ≤ 0 :=
  coneForm_nonpos_of_contraction _ _ _ _ (by positivity)
    (slowTailRatio_strict_cone σ ℓ K q s hσ hK hq hsre hsim) hρ hρ1

end DefocusingNLS

end OAI
