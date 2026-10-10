import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileNormalizedBounds

namespace OAI

/-! The finite certificate gives a uniform nonzero first matching component. -/

namespace DefocusingNLS.ProfileCertificate

private theorem gap_of_near (a b u s s₀ : ℂ) (χ ρ e U D : ℝ)
    (hρ : 0 ≤ ρ) (he : 0 ≤ e)
    (hb : ‖b-1‖ ≤ χ) (ha : ‖a-u‖ ≤ χ) (hu : ‖u‖ ≤ U)
    (hs : ‖s‖ ≤ ρ) (hs₀ : ‖s-s₀‖ ≤ e) (hD : D ≤ ‖1-s₀*u‖) :
    D-(χ+ρ*χ+e*U)-ρ*(U+χ) ≤ ‖b-s*a‖-‖s‖*‖a‖ := by
  have hn : ‖a‖ ≤ U+χ := by
    have ht : ‖a‖ ≤ ‖a-u‖+‖u‖ := by
      calc
        _ = ‖(a-u)+u‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have hid : 1-s₀*u = (b-s*a)-((b-1)-s*(a-u)-(s-s₀)*u) := by ring
  have hd : ‖1-s₀*u‖ ≤ ‖b-s*a‖+χ+ρ*χ+e*U := by
    rw [hid]
    calc
      _ ≤ ‖b-s*a‖+‖(b-1)-s*(a-u)-(s-s₀)*u‖ := norm_sub_le _ _
      _ ≤ ‖b-s*a‖+(‖b-1‖+‖s*(a-u)‖+‖(s-s₀)*u‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by
        rw [norm_mul, norm_mul]
        have h₁ := mul_le_mul hs ha (norm_nonneg _) hρ
        have h₂ := mul_le_mul hs₀ hu (norm_nonneg _) he
        linarith
  have hm : ‖s‖*‖a‖ ≤ ρ*(U+χ) :=
    mul_le_mul hs hn (norm_nonneg _) hρ
  linarith

theorem normalized_denominator_gap (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    (6/10 : ℝ) <
      ‖normalizedProfile b z 0 1-
        (Complex.I*((centerZ : ℝ)+z)/5)*normalizedProfile b z 0 0‖-
      (((centerZ : ℝ)+z)/5)*‖normalizedProfile b z 0 0‖ := by
  have hρ : 0 ≤ ((centerZ : ℝ)+(radius : ℝ))/5 := by norm_num [centerZ, radius]
  have he : 0 ≤ (radius : ℝ)/5 := by norm_num [radius]
  have hZ : 0 ≤ (centerZ : ℝ)+z := by
    have h := (abs_le.mp hz).1
    norm_num [centerZ, radius] at h ⊢
    linarith
  have hs : ‖Complex.I*((centerZ : ℝ)+z)/5‖ ≤ ((centerZ : ℝ)+(radius : ℝ))/5 := by
    simp only [← Complex.ofReal_add, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_ofNat, abs_of_nonneg hZ]
    linarith [(abs_le.mp hz).2]
  have hdiff : ‖Complex.I*((centerZ : ℝ)+z)/5-Complex.I*(centerZ : ℝ)/5‖ ≤ (radius : ℝ)/5 := by
    have heq : Complex.I*((centerZ : ℝ)+z)/5-Complex.I*(centerZ : ℝ)/5 = Complex.I*z/5 := by
      push_cast; ring
    rw [heq]
    simp only [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_ofNat]
    linarith
  have hg := gap_of_near (normalizedProfile b z 0 0) (normalizedProfile b z 0 1)
    (centralNormalized 0 0) (Complex.I*((centerZ : ℝ)+z)/5)
    (Complex.I*(centerZ : ℝ)/5) (changeBound : ℝ)
    (((centerZ : ℝ)+(radius : ℝ))/5) ((radius : ℝ)/5) (318/100) (234/100)
    hρ he
    (by simpa only [centralNormalized_zero_one] using (normalizedProfile_variation b z hb hz 0 1).le)
    (normalizedProfile_variation b z hb hz 0 0).le central_u_bound.le hs hdiff
    central_denominator_bound.le
  have hcert : (6/10 : ℝ) < (denominatorGap : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr propagation_comparisons.1
  have hid : (denominatorGap : ℝ) =
      234/100-((changeBound : ℝ)+(((centerZ : ℝ)+(radius : ℝ))/5)*(changeBound : ℝ)+
        ((radius : ℝ)/5)*(318/100))-
      (((centerZ : ℝ)+(radius : ℝ))/5)*(318/100+(changeBound : ℝ)) := by
    unfold denominatorGap
    push_cast
    ring
  rw [hid] at hcert
  have hsnorm : ‖Complex.I*((centerZ : ℝ)+z)/5‖ = ((centerZ : ℝ)+z)/5 := by
    simp only [← Complex.ofReal_add, norm_div, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, abs_of_nonneg hZ]
  rw [hsnorm] at hg
  exact hcert.trans_le hg

end DefocusingNLS.ProfileCertificate

end OAI
