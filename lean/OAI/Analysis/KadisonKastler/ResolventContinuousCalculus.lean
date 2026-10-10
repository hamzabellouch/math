import OAI.Analysis.KadisonKastler.ResolventComplexMeasure

namespace OAI

/-! # Continuous spectral coordinates on the real resolvent spectrum -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventContinuousCalculus (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    C(spectrum ℝ R, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (cfcHom hR.isStarNormal).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ
      ⟨fun z => ⟨z.val.re, hR.spectrumRestricts.subset_preimage z.property⟩,
        (Complex.continuous_re.comp continuous_subtype_val).subtype_mk _⟩)

theorem resolventContinuousCalculus_eq_cfc (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (f : ℝ → ℂ) (hf : ContinuousOn f (spectrum ℝ R)) :
    resolventContinuousCalculus R hR ⟨fun s => f s.val, hf.domRestrict⟩ =
      cfc (fun z : ℂ => f z.re) R := by
  exact (cfc_apply _ R hR.isStarNormal
    (hf.comp Complex.continuous_re.continuousOn hR.spectrumRestricts.subset_preimage)).symm

theorem resolventContinuousCalculus_ofReal (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (f : C(spectrum ℝ R, ℝ)) :
    resolventContinuousCalculus R hR
      ⟨fun s => (f s : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ = cfcHom hR f := by
  have hs : SpectrumRestricts R (⟨Complex.re, Complex.continuous_re⟩ : C(ℂ, ℝ)) :=
    hR.spectrumRestricts
  rw [SpectrumRestricts.cfcHom_eq_restrict _ hR hR.isStarNormal hs]
  rfl

def resolventContinuousVector (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    C(spectrum ℝ R, ℂ) →ₗ[ℂ] H where
  toFun f := resolventContinuousCalculus R hR f x
  map_add' f g := by rw [map_add, add_apply]
  map_smul' c f := by rw [map_smul, smul_apply, RingHom.id_apply]

theorem resolventContinuousVector_norm_sq (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℂ)) :
    ‖resolventContinuousVector R hR x f‖ ^ 2 =
      ∫ s, ‖f s‖ ^ 2 ∂resolventVectorMeasure R hR x := by
  let g : C(spectrum ℝ R, ℝ) := ⟨fun s => ‖f s‖ ^ 2, f.continuous.norm.pow 2⟩
  have hg : (⟨fun s => (g s : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ :
      C(spectrum ℝ R, ℂ)) = star f * f := by
    ext s
    change ((‖f s‖ ^ 2 : ℝ) : ℂ) = star (f s) * f s
    have hn := RCLike.conj_mul (f s)
    change star (f s) * f s = (‖f s‖ : ℂ) ^ 2 at hn
    rw [Complex.ofReal_pow]
    exact hn.symm
  have hop := resolventContinuousCalculus_ofReal R hR g
  rw [hg, map_mul, map_star] at hop
  have hi := resolventVectorMeasure_integral R hR x g
  rw [← hop] at hi
  change (∫ s, ‖f s‖ ^ 2 ∂resolventVectorMeasure R hR x) =
    RCLike.re (inner ℂ x ((star (resolventContinuousCalculus R hR f) *
      resolventContinuousCalculus R hR f) x)) at hi
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq] at hi
  exact hi.symm

end

end KadisonKastler

end OAI
