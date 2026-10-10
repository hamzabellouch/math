import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HermitianBoundaryForm

namespace OAI

/-! # The Hermitian matrix represented by a finite forward cone -/

open Matrix

namespace DefocusingNLS

noncomputable def forwardFormEntry (M : ℝ) (s : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 2) : ℂ :=
  (M : ℂ) * star (T 0 i) * T 0 j +
    s * (star (T 0 i) * T 1 j - star (T 1 i) * T 0 j)

theorem star_eq_neg_of_re_zero (s : ℂ) (hs : s.re = 0) : star s = -s := by
  apply Complex.ext <;> simp [hs]

theorem forwardFormEntry_hermitian (M : ℝ) (s : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hs : s.re = 0) (i j : Fin 2) : star (forwardFormEntry M s T j i) = forwardFormEntry M s T i j := by
  have hM : star (M : ℂ) = (M : ℂ) := Complex.conj_ofReal M
  simp only [forwardFormEntry, star_add, star_mul, star_sub, star_star,
    star_eq_neg_of_re_zero s hs, hM]
  ring

theorem forwardFormEntry_diagonal (M : ℝ) (s : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hs : s.re = 0) (i : Fin 2) : forwardFormEntry M s T i i =
      ((forwardFormEntry M s T i i).re : ℂ) := by
  have h := congrArg Complex.im (forwardFormEntry_hermitian M s T hs i i)
  simp only [Complex.star_def, Complex.conj_im] at h
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

theorem coneForm_as_hermitian (M : ℝ) (s u v : ℂ) (hs : s.re = 0) :
    ((M : ℂ) * star u * u + s * (star u * v - star v * u)).re = 2 * coneForm M s u v := by
  simp only [coneForm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hs]
  ring

theorem hermitianPairForm_eq_quadratic (a d : ℝ) (c u v : ℂ) :
    hermitianPairForm a d c u v =
      ((a : ℂ) * star u * u + c * star u * v + star c * star v * u +
        (d : ℂ) * star v * v).re := by
  simp only [hermitianPairForm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem forwardFormEntry_expansion (M : ℝ) (s u v : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    forwardFormEntry M s T 0 0 * star u * u +
      forwardFormEntry M s T 0 1 * star u * v +
      forwardFormEntry M s T 1 0 * star v * u +
      forwardFormEntry M s T 1 1 * star v * v =
    (M : ℂ) * star ((T *ᵥ ![u, v]) 0) * ((T *ᵥ ![u, v]) 0) +
      s * (star ((T *ᵥ ![u, v]) 0) * ((T *ᵥ ![u, v]) 1) -
        star ((T *ᵥ ![u, v]) 1) * ((T *ᵥ ![u, v]) 0)) := by
  simp [forwardFormEntry, Matrix.mulVec, dotProduct, Fin.sum_univ_two, star_add, star_mul]
  ring

/-- The Hermitian quadratic form is twice the forward cone form. -/
theorem forwardFormEntry_pairForm (M : ℝ) (s : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hs : s.re = 0) (u v : ℂ) :
    hermitianPairForm (forwardFormEntry M s T 0 0).re (forwardFormEntry M s T 1 1).re
      (forwardFormEntry M s T 0 1) u v = 2 * matrixCone M s T ![u, v] := by
  rw [hermitianPairForm_eq_quadratic,
    ← forwardFormEntry_diagonal M s T hs 0, ← forwardFormEntry_diagonal M s T hs 1,
    forwardFormEntry_hermitian M s T hs 1 0, forwardFormEntry_expansion,
    coneForm_as_hermitian M s _ _ hs]
  rfl

theorem hermitianPairForm_add (a₁ a₂ d₁ d₂ : ℝ) (c₁ c₂ u v : ℂ) :
    hermitianPairForm (a₁ + a₂) (d₁ + d₂) (c₁ + c₂) u v =
      hermitianPairForm a₁ d₁ c₁ u v + hermitianPairForm a₂ d₂ c₂ u v := by
  simp only [hermitianPairForm, add_mul, Complex.add_re]
  ring

/-- Positive leading entry and determinant of the summed Hermitian matrix
supply the positivity needed for exclusion of matching zeros. -/
theorem positive_sum_matrixCone (M : ℝ) (s₁ s₂ : ℂ)
    (T₁ T₂ : Matrix (Fin 2) (Fin 2) ℂ) (hs₁ : s₁.re = 0) (hs₂ : s₂.re = 0)
    (ha : 0 < (forwardFormEntry M s₁ T₁ 0 0).re + (forwardFormEntry M s₂ T₂ 0 0).re)
    (hdet : 0 <
      ((forwardFormEntry M s₁ T₁ 0 0).re + (forwardFormEntry M s₂ T₂ 0 0).re) *
      ((forwardFormEntry M s₁ T₁ 1 1).re + (forwardFormEntry M s₂ T₂ 1 1).re) -
      Complex.normSq (forwardFormEntry M s₁ T₁ 0 1 + forwardFormEntry M s₂ T₂ 0 1))
    (w : Fin 2 → ℂ) (hw : w ≠ 0) :
    0 < matrixCone M s₁ T₁ w + matrixCone M s₂ T₂ w := by
  have hw' : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hw
    ext i
    fin_cases i <;> simp [hn.1, hn.2]
  have h := hermitianPairForm_pos _ _ _ (w 0) (w 1) ha hdet hw'
  rw [hermitianPairForm_add, forwardFormEntry_pairForm M s₁ T₁ hs₁,
    forwardFormEntry_pairForm M s₂ T₂ hs₂] at h
  have he : ![w 0, w 1] = w := by ext i; fin_cases i <;> rfl
  rw [he] at h
  linarith

end DefocusingNLS

end OAI
