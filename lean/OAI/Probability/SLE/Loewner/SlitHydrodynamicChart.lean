import OAI.Probability.SLE.Geometry.ExteriorLaurent

namespace OAI

/-! Static hydrodynamic normalization for the complement of an arbitrary
simple attached arc. No time parametrization or Loewner equation is asserted. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma positive_real_affine_halfPlane {a : ℝ} (ha : 0<a) (b : ℝ) :
    BijOn (fun z : ℂ => (a:ℂ)*z-(b:ℂ)) upperHalfPlane upperHalfPlane := by
  have ha0 : (a:ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  refine ⟨?_,?_,?_⟩
  · intro z hz
    change 0 < ((a:ℂ)*z-(b:ℂ)).im
    simpa only [sub_im,mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,sub_zero]
      using mul_pos ha hz
  · intro z _ w _ he
    apply mul_left_cancel₀ ha0
    simpa only [sub_add_cancel] using congrArg (fun x : ℂ => x+(b:ℂ)) he
  · intro z hz
    refine ⟨(z+(b:ℂ))/(a:ℂ),?_,?_⟩
    · change 0 < ((z+(b:ℂ))/(a:ℂ)).im
      have he : ((z+(b:ℂ))/(a:ℂ)).im=z.im/a := by
        rw [div_ofReal_im,add_im,ofReal_im,add_zero]
      rw [he]
      exact div_pos hz ha
    · field_simp
      ring

lemma eq_ofReal_re_of_conj_eq {z : ℂ} (hz : conj z=z) : z=(z.re:ℂ) := by
  have hi := congrArg Complex.im hz
  simp only [conj_im] at hi
  apply Complex.ext
  · simp
  · simp only [ofReal_im]
    linarith

def slitHydrodynamicMap (f : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  (a:ℂ)*exteriorJoukowski (slitExteriorMap f z)-deriv (slitInfinityFactor f a) 0

theorem simple_slit_exists_hydrodynamic_chart
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ (G F : ℂ → ℂ) (c : ℝ),
      BijOn G (upperHalfPlane \ range p) upperHalfPlane ∧
      DifferentiableOn ℂ G (upperHalfPlane \ range p) ∧
      DifferentiableOn ℂ F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane \ range p, F (G z)=z) ∧
      (∀ z ∈ upperHalfPlane, G (F z)=z) ∧
      Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)) := by
  obtain ⟨f,a,ha,hb,hf,hf0,hfa,hs,hu⟩ :=
    reflected_slit_exists_normalized_chart p hi h0 hH
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have hD : invertedExterior (reflectedArcSet p) ∈ 𝓝 (0:ℂ) :=
    (invertedExterior_isOpen hK).mem_nhds (zero_mem_invertedExterior _)
  have hfa' : AnalyticAt ℂ f 0 := hf.analyticAt hD
  have hsH := slitInfinityFactor_reflection hD hs a
  have hreal := eq_ofReal_re_of_conj_eq (derivative_real_of_reflection hD hsH)
  have hsQ := dslope_reflection hD hsH
  have hc := eq_ofReal_re_of_conj_eq (derivative_real_of_reflection hD hsQ)
  let G := slitHydrodynamicMap f a
  have hG : BijOn G (upperHalfPlane \ range p) upperHalfPlane := by
    have hh := (positive_real_affine_halfPlane ha (deriv (slitInfinityFactor f a) 0).re).comp
      (exteriorJoukowski_bijOn.comp (slitExteriorMap_bijOn p h0 hH hs hu))
    apply hh.congr
    intro z _
    change (a:ℂ)*exteriorJoukowski (slitExteriorMap f z)-
      ((deriv (slitInfinityFactor f a) 0).re:ℂ)=
      (a:ℂ)*exteriorJoukowski (slitExteriorMap f z)-deriv (slitInfinityFactor f a) 0
    rw [← hreal]
  have hdiff : DifferentiableOn ℂ G (upperHalfPlane \ range p) := by
    have he := exteriorJoukowski_differentiableOn.comp
      (slitExteriorMap_differentiableOn p h0 hH hf hb.injOn hf0)
      (slitExteriorMap_bijOn p h0 hH hs hu).mapsTo
    exact (he.const_mul (a:ℂ)).sub_const _
  have ho : IsOpen (upperHalfPlane \ range p) :=
    isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed
  let F := invFunOn G (upperHalfPlane \ range p)
  have hF : DifferentiableOn ℂ F upperHalfPlane := by
    have hh := hdiff.invFunOn ho hG.injOn
    simpa only [F,hG.image_eq] using hh
  refine ⟨G,F,(deriv (dslope (slitInfinityFactor f a) 0) 0).re,hG,hdiff,hF,
    fun z hz => hG.injOn.leftInvOn_invFunOn hz,
    fun z hz => hG.surjOn.rightInvOn_invFunOn hz,?_⟩
  have ht := slitExteriorMap_laurent_limit hfa' hf0 ha.ne' hfa
  rw [hc] at ht
  exact ht

end SLEExactGauge

end

end OAI
