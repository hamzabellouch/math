import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicPhase

namespace OAI

/-! The exact complex form recovered by testing the real variational equation with v and i v. -/

namespace DefocusingNLS

private theorem compatible_re_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [InnerProductSpace ℝ E] (x y : E) :
    (inner ℂ x y).re=inner ℝ x y := by
  exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (𝕜 := ℂ) x y).trans
      (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y).symm

noncomputable def spectralHarmonicComplexForm (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (u v : SpectralHarmonicEnergy ell R) : ℂ :=
  let V := (spectralRadialValue R).comp (spectralHarmonicRadialForget ell R)
  let D := (spectralRadialDerivative R).comp (spectralHarmonicRadialForget ell R)
  let G := spectralHarmonicAngularValue ell R
  let P := spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound
  let A := spectralL2ComplexMultiplier (spectralAngularMeasure R) w.density
    w.angular_measurable w.bound w.angular_bound
  inner ℂ (P (V u)) (V v) + inner ℂ (P (D u)) (D v) + inner ℂ (A (G u)) (G v)

noncomputable def spectralHarmonicPairComplexForm (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (u v : SpectralHarmonicPair ell R) : ℂ :=
  spectralHarmonicComplexForm ell R w u.fst v.fst +
    spectralHarmonicComplexForm ell R w u.snd v.snd

theorem spectralHarmonicComplexForm_re (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (u v : SpectralHarmonicEnergy ell R) :
    (spectralHarmonicComplexForm ell R w u v).re=spectralHarmonicForm ell R w u v := by
  simp only [spectralHarmonicComplexForm,Complex.add_re,compatible_re_inner]
  rfl

theorem spectralHarmonicPairComplexForm_re (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (u v : SpectralHarmonicPair ell R) :
    (spectralHarmonicPairComplexForm ell R w u v).re=spectralHarmonicPairForm ell R w u v := by
  simp only [spectralHarmonicPairComplexForm,Complex.add_re,spectralHarmonicComplexForm_re]
  rfl

theorem spectralHarmonicComplexForm_smul_right (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (u v : SpectralHarmonicEnergy ell R) (c : ℂ) :
    spectralHarmonicComplexForm ell R w u (c • v)=c*spectralHarmonicComplexForm ell R w u v := by
  simp only [spectralHarmonicComplexForm,map_smul,inner_smul_right]
  ring

theorem spectralHarmonicPairComplexForm_smul_right (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (u v : SpectralHarmonicPair ell R) (c : ℂ) :
    spectralHarmonicPairComplexForm ell R w u (c • v)=c*spectralHarmonicPairComplexForm ell R w u v := by
  change spectralHarmonicComplexForm ell R w u.fst (c • v.fst)+
    spectralHarmonicComplexForm ell R w u.snd (c • v.snd)=_
  rw [spectralHarmonicComplexForm_smul_right,spectralHarmonicComplexForm_smul_right]
  exact (mul_add _ _ _).symm

theorem spectralHarmonicPairComplexForm_of_real (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (u v F : SpectralHarmonicPair ell R)
    (h : spectralHarmonicPairForm ell R w u v=inner ℝ F v)
    (hi : spectralHarmonicPairForm ell R w u (Complex.I • v)=inner ℝ F (Complex.I • v)) :
    spectralHarmonicPairComplexForm ell R w u v=inner ℂ F v := by
  apply Complex.ext
  · rw [spectralHarmonicPairComplexForm_re,compatible_re_inner]
    exact h
  · rw [← spectralHarmonicPairComplexForm_re,spectralHarmonicPairComplexForm_smul_right] at hi
    change (Complex.I*spectralHarmonicPairComplexForm ell R w u v).re=
      (inner ℂ F (Complex.I • v)).re at hi
    have hip : inner ℂ F (Complex.I • v)=Complex.I*inner ℂ F v :=
      inner_smul_right F v Complex.I
    rw [hip] at hi
    simpa only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,
      neg_inj] using hi

theorem spectralHarmonicPairInner_re (ell : ℕ) (R : ℝ)
    (u v : SpectralHarmonicPair ell R) : (inner ℂ u v).re=inner ℝ u v :=
  compatible_re_inner u v

end DefocusingNLS

end OAI
