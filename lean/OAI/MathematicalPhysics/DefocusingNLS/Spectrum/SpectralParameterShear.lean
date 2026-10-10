import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPointFieldParameter

namespace OAI

/-! Removing the parameter derivative of the radial power converts the
normalized source to the physical Jordan source. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularParameterShear (t : ℝ) (Y D : E₄) : E₄ :=
  D - (2 * (t : ℂ)) • Y - ((0, 2 * Y.1.1), (0, 2 * Y.2.1))

theorem circularParameterShear_hasDerivAt (νp νm η : ℂ) (m : ℕ) (q : ℂ)
    (Y D : ℝ → E₄) (t : ℝ)
    (hY : HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm η m q (Y t)) t)
    (hD : HasDerivAt D (circularLeadingField t (D t) +
      circularBoundedField νp νm η m q (D t) + circularPointSlopeCLM νp νm 0 (Y t)) t) :
    HasDerivAt (fun s => circularParameterShear s (Y s) (D s))
      (circularLeadingField t (circularParameterShear t (Y t) (D t)) +
        circularBoundedField νp νm η m q (circularParameterShear t (Y t) (D t)) +
        ((0, -Complex.I * (Real.exp (2 * t) : ℂ) * (Y t).1.1),
         (0, Complex.I * (Real.exp (2 * t) : ℂ) * (Y t).2.1))) t := by
  have hp := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  have hm := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  have hp0 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hp
  have hm0 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hm
  have he := ((hasDerivAt_const t (0 : ℂ)).prodMk (hp0.const_mul 2)).prodMk
    ((hasDerivAt_const t (0 : ℂ)).prodMk (hm0.const_mul 2))
  have hs := (hasDerivAt_id t).ofReal_comp.const_mul (2 : ℂ)
  have hd := (hD.sub (hs.smul hY)).sub he
  apply hd.congr_deriv
  simp only [id_eq, Complex.ofReal_one, mul_one, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  change (circularLeadingField t (D t) + circularBoundedField νp νm η m q (D t) +
      circularPointSlopeCLM νp νm 0 (Y t)) -
      ((2 * (t : ℂ)) •
        (circularLeadingField t (Y t) + circularBoundedField νp νm η m q (Y t)) + (2 : ℂ) • Y t) -
      ((0, 2 * (circularLeadingField t (Y t) + circularBoundedField νp νm η m q (Y t)).1.1),
       (0, 2 * (circularLeadingField t (Y t) + circularBoundedField νp νm η m q (Y t)).2.1)) = _
  change (circularLeadingField t (D t) + circularBoundedField νp νm η m q (D t) +
      ((0, 4 * (Y t).1.2 + (4 * (νp - 2 * 0) + 20) * (Y t).1.1),
       (0, 4 * (Y t).2.2 + (4 * (νm - 2 * 0) + 20) * (Y t).2.1))) -
      ((2 * (t : ℂ)) •
        (circularLeadingField t (Y t) + circularBoundedField νp νm η m q (Y t)) + (2 : ℂ) • Y t) -
      ((0, 2 * (circularLeadingField t (Y t) + circularBoundedField νp νm η m q (Y t)).1.1),
       (0, 2 * (circularLeadingField t (Y t) + circularBoundedField νp νm η m q (Y t)).2.1)) = _
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [circularParameterShear, circularLeadingField, circularBoundedField,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    push_cast
    ring

end DefocusingNLS

end OAI
