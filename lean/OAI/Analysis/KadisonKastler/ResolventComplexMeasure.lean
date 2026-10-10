import OAI.Analysis.KadisonKastler.ResolventVectorMeasure

namespace OAI

/-! # Complex coefficients of the resolvent vector measure -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventVectorMeasure_integral_real (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ R)) :
    ((∫ s, f s.val ∂resolventVectorMeasure R hR x : ℝ) : ℂ) =
      inner ℂ x (cfc f R x) := by
  have hi := resolventVectorMeasure_integral R hR x ⟨_, hf.domRestrict⟩
  rw [← cfc_apply f R hR hf] at hi
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.cfc (a := R) (f := f))).im_inner_self_apply x
  change (inner ℂ x (cfc f R x)).im = 0 at hs
  apply Complex.ext
  · exact hi
  · simpa only [Complex.ofReal_im] using hs.symm

theorem resolventComplexCFC_split (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (f : ℝ → ℂ) (hf : ContinuousOn f (spectrum ℝ R)) :
    cfc (fun z : ℂ => f z.re) R = cfc (fun s => (f s).re) R +
      Complex.I • cfc (fun s => (f s).im) R := by
  have hm : Set.MapsTo Complex.re (spectrum ℂ R) (spectrum ℝ R) :=
    fun _ hz => hR.spectrumRestricts.subset_preimage hz
  have hr : ContinuousOn (fun z : ℂ => ((f z.re).re : ℂ)) (spectrum ℂ R) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((Complex.continuous_re.comp_continuousOn hf).comp Complex.continuous_re.continuousOn hm)
  have hi : ContinuousOn (fun z : ℂ => ((f z.re).im : ℂ)) (spectrum ℂ R) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((Complex.continuous_im.comp_continuousOn hf).comp Complex.continuous_re.continuousOn hm)
  rw [cfc_real_eq_complex (fun s => (f s).re) hR,
    cfc_real_eq_complex (fun s => (f s).im) hR,
    ← cfc_const_mul Complex.I (fun z : ℂ => ((f z.re).im : ℂ)) R hi,
    ← cfc_add _ (fun z : ℂ => ((f z.re).re : ℂ))
      (fun z : ℂ => Complex.I * ((f z.re).im : ℂ)) hr (continuousOn_const.mul hi)]
  apply cfc_congr
  intro z _
  exact (by simpa only [mul_comm Complex.I] using (Complex.re_add_im (f z.re)).symm)

theorem resolventVectorMeasure_integral_complex (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : ℝ → ℂ) (hf : ContinuousOn f (spectrum ℝ R)) :
    (∫ s, f s.val ∂resolventVectorMeasure R hR x) =
      inner ℂ x (cfc (fun z : ℂ => f z.re) R x) := by
  have hint : Integrable (fun s : spectrum ℝ R => f s.val) (resolventVectorMeasure R hR x) :=
    hf.domRestrict.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [resolventComplexCFC_split R hR f hf, add_apply, smul_apply, inner_add_right,
    inner_smul_right, ← resolventVectorMeasure_integral_real R hR x (fun s : ℝ => (f s).re)
      (Complex.continuous_re.comp_continuousOn hf),
    ← resolventVectorMeasure_integral_real R hR x (fun s : ℝ => (f s).im)
      (Complex.continuous_im.comp_continuousOn hf)]
  have hi := integral_re_add_im hint
  change ((∫ s, (f s.val).re ∂resolventVectorMeasure R hR x : ℝ) : ℂ) +
    ((∫ s, (f s.val).im ∂resolventVectorMeasure R hR x : ℝ) : ℂ) * Complex.I = _ at hi
  simpa only [mul_comm Complex.I] using hi.symm

end

end KadisonKastler

end OAI
