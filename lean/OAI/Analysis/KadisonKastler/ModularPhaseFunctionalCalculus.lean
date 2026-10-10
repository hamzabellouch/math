import OAI.Analysis.KadisonKastler.GraphResolventFunctionalCalculus

namespace OAI

/-! # Weighted norm convergence of the modular phases

Complex continuous functional calculus turns the scalar phase bound into
an operator bound on the dense range of `R(1-R)`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def modularPhaseScalar (t ε : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((t : ℂ) * (regularizedLogScalar ε z.re : ℂ)))

theorem regularizedLogScalar_complex_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun z : ℂ => (regularizedLogScalar ε z.re : ℂ))
      (spectrum ℂ (graphResolvent M J Ω 1)) := by
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  exact Complex.continuous_ofReal.comp_continuousOn
    ((regularizedLogScalar_continuousOn J Ω hε).comp
      Complex.continuous_re.continuousOn hR.spectrumRestricts.subset_preimage)

theorem modularPhaseScalar_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (modularPhaseScalar t ε) (spectrum ℂ (graphResolvent M J Ω 1)) :=
  Complex.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (continuousOn_const.mul
      (regularizedLogScalar_complex_continuousOn J Ω hε)))

theorem regularizedModularGroup_eq_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      cfc (modularPhaseScalar t ε) (graphResolvent M J Ω 1) := by
  let R := graphResolvent M J Ω 1
  let f : ℂ → ℂ := fun z => Complex.I * ((t : ℂ) * (regularizedLogScalar ε z.re : ℂ))
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hl := regularizedLogScalar_complex_continuousOn (M := M) J Ω hε
  have hf : ContinuousOn f (spectrum ℂ R) :=
    continuousOn_const.mul (continuousOn_const.mul hl)
  have hc : cfc f R = Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val) := by
    unfold f
    rw [cfc_const_mul Complex.I (fun z : ℂ => (t : ℂ) * (regularizedLogScalar ε z.re : ℂ)) R
      (continuousOn_const.mul hl),
      cfc_const_mul (t : ℂ) (fun z : ℂ => (regularizedLogScalar ε z.re : ℂ)) R hl,
      ← cfc_real_eq_complex (regularizedLogScalar ε) hR,
      ← regularizedModularLog_eq_cfc J Ω hε]
  change NormedSpace.exp (Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val)) = _
  rw [← hc, ← CFC.complex_exp_eq_normedSpace_exp (cfc_predicate f R),
    ← cfc_comp Complex.exp f R hR.isStarNormal Complex.continuous_exp.continuousOn hf]
  rfl

theorem graphResolventCutoff_eq_complex_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    graphResolventCutoff M J Ω =
      cfc (fun z : ℂ => (z.re * (1 - z.re) : ℝ)) (graphResolvent M J Ω 1) := by
  rw [graphResolventCutoff_eq_cfc,
    cfc_real_eq_complex _ (graphResolvent_positive J Ω 1).isSelfAdjoint]

/-- A bound uniform in the spectral parameter, after the dense cutoff. -/
theorem regularizedModularGroup_weighted_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ‖((regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) -
      (regularizedModularGroup M J Ω δ (Multiplicative.ofAdd t) : H →L[ℂ] H)) *
      graphResolventCutoff M J Ω‖ ≤ |t| * |ε - δ| := by
  have he := modularPhaseScalar_continuousOn (M := M) J Ω t hε
  have hd := modularPhaseScalar_continuousOn (M := M) J Ω t hδ
  rw [regularizedModularGroup_eq_cfc J Ω t hε, regularizedModularGroup_eq_cfc J Ω t hδ,
    graphResolventCutoff_eq_complex_cfc, ← cfc_sub _ _ _ he hd,
    ← cfc_mul (fun z => modularPhaseScalar t ε z - modularPhaseScalar t δ z)
      (fun z : ℂ => (z.re * (1 - z.re) : ℝ)) _ (he.sub hd) (by fun_prop)]
  apply norm_cfc_le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  intro z hz
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  have hb := graphResolvent_spectrum_bounds J Ω (hR.spectrumRestricts.subset_preimage hz)
  change 0 ≤ z.re ∧ z.re ≤ 1 at hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb.2)), mul_comm]
  simpa only [modularPhaseScalar, Complex.ofReal_mul] using
    weighted_modularPhase_difference t z.re ε δ hb.1 hb.2 hε hδ

theorem regularizedModularGroup_cutoff_apply_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (t : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (x : H) :
    ‖(regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (graphResolventCutoff M J Ω x) -
      (regularizedModularGroup M J Ω δ (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (graphResolventCutoff M J Ω x)‖ ≤ |t| * |ε - δ| * ‖x‖ := by
  change ‖(((regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) -
    (regularizedModularGroup M J Ω δ (Multiplicative.ofAdd t) : H →L[ℂ] H)) *
      graphResolventCutoff M J Ω) x‖ ≤ _
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (regularizedModularGroup_weighted_bound J Ω t hε hδ)
      (norm_nonneg x))

end

end KadisonKastler

end OAI
