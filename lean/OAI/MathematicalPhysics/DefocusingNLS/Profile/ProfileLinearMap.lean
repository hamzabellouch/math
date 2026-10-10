import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileCertificateComparisons
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ParameterOpenness

namespace OAI

/-! The real-linear map certified at the free profile center. -/

namespace DefocusingNLS.ProfileCertificate

noncomputable def realLinearMap (x y : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight x + Complex.imCLM.smulRight y

@[simp] theorem realLinearMap_apply (x y z : ℂ) :
    realLinearMap x y z = (z.re : ℂ)*x+(z.im : ℂ)*y := by
  simp [realLinearMap, Complex.real_smul]

/-- The two strict rational Gram inequalities give the Euclidean lower bound. -/
theorem realLinearMap_minimum_stretch (x y : ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hx : c^2 < Complex.normSq x)
    (hgram : (Complex.normSq x-c^2)*(Complex.normSq y-c^2) >
      (x.re*y.re+x.im*y.im)^2) (z : ℂ) :
    c*‖z‖ ≤ ‖realLinearMap x y z‖ := by
  let A := Complex.normSq x-c^2
  let B := Complex.normSq y-c^2
  let C := x.re*y.re+x.im*y.im
  have hA : 0 < A := sub_pos.mpr hx
  have hD : 0 ≤ A*B-C^2 := le_of_lt (sub_pos.mpr hgram)
  have he : A*(Complex.normSq (realLinearMap x y z)-c^2*Complex.normSq z) =
      (A*z.re+C*z.im)^2+(A*B-C^2)*z.im^2 := by
    simp only [realLinearMap_apply, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, A, B, C]
    ring
  have hnon : 0 ≤ A*(Complex.normSq (realLinearMap x y z)-c^2*Complex.normSq z) := by
    rw [he]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hD (sq_nonneg _))
  have hq := nonneg_of_mul_nonneg_right hnon hA
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hq
  have hcz : 0 ≤ c*‖z‖ := mul_nonneg hc (norm_nonneg _)
  nlinarith [norm_nonneg (realLinearMap x y z)]

noncomputable def centralX : ℂ :=
  RationalComplex.toComplex (RationalComplex.quotient result.derivB.d result.value.b)
noncomputable def centralY : ℂ :=
  RationalComplex.toComplex (RationalComplex.quotient result.derivZ.d result.value.b)

/-- The concrete map has the precise lower bound needed in the degree argument. -/
theorem central_minimum_stretch (z : ℂ) :
    (48/1000 : ℝ)*‖z‖ ≤ ‖realLinearMap centralX centralY z‖ := by
  have h := linear_bounds
  rcases h with ⟨hx, hgram, _⟩
  apply realLinearMap_minimum_stretch centralX centralY (48/1000) (by norm_num) _ _ z
  · simp only [centralX, RationalComplex.normSq_toComplex]
    have hh := (Rat.cast_lt (K := ℝ)).mpr hx
    push_cast at hh ⊢
    exact hh
  · simp only [centralX, centralY, RationalComplex.normSq_toComplex,
      RationalComplex.toComplex_re, RationalComplex.toComplex_im]
    have hh := (Rat.cast_lt (K := ℝ)).mpr hgram
    push_cast at hh ⊢
    exact hh

theorem central_linear_orientation :
    centralX.re*centralY.im-centralX.im*centralY.re < 0 := by
  have h := linear_bounds
  rcases h with ⟨_, _, _, _, _, _, hdet⟩
  simp only [centralX, centralY, RationalComplex.toComplex_re, RationalComplex.toComplex_im]
  exact_mod_cast hdet

end DefocusingNLS.ProfileCertificate

end OAI
