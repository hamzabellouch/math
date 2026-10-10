import OAI.Probability.SLE.Loewner.HydrodynamicCoefficient

namespace OAI

/-! Nonnegative capacity and height comparison for the exact normalized
chart of a finite simple attached slit. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

theorem simple_slit_exists_nonnegative_capacity_chart
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ (G F : ℂ → ℂ) (c : ℝ), 0≤c ∧
      BijOn G (upperHalfPlane \ range p) upperHalfPlane ∧
      DifferentiableOn ℂ G (upperHalfPlane \ range p) ∧
      DifferentiableOn ℂ F upperHalfPlane ∧
      MapsTo F upperHalfPlane (upperHalfPlane \ range p) ∧
      (∀ z ∈ upperHalfPlane \ range p, F (G z)=z) ∧
      (∀ z ∈ upperHalfPlane, G (F z)=z) ∧
      Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)) ∧
      Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) ∧
      (∀ z ∈ upperHalfPlane \ range p, (G z).im ≤ z.im) := by
  obtain ⟨f,a,ha,hb,hf,hf0,hfa,hs,hu⟩ :=
    reflected_slit_exists_normalized_chart p hi h0 hH
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have hD : invertedExterior (reflectedArcSet p) ∈ 𝓝 (0:ℂ) :=
    (invertedExterior_isOpen hK).mem_nhds (zero_mem_invertedExterior _)
  have hreal := eq_ofReal_re_of_conj_eq (derivative_real_of_reflection hD
    (slitInfinityFactor_reflection hD hs a))
  let G := slitHydrodynamicMap f a
  have hG : BijOn G (upperHalfPlane \ range p) upperHalfPlane := by
    apply ((positive_real_affine_halfPlane ha (deriv (slitInfinityFactor f a) 0).re).comp
      (exteriorJoukowski_bijOn.comp (slitExteriorMap_bijOn p h0 hH hs hu))).congr
    intro z _
    change (a:ℂ)*exteriorJoukowski (slitExteriorMap f z)-
      ((deriv (slitInfinityFactor f a) 0).re:ℂ)=
      (a:ℂ)*exteriorJoukowski (slitExteriorMap f z)-deriv (slitInfinityFactor f a) 0
    rw [← hreal]
  have hdG : DifferentiableOn ℂ G (upperHalfPlane \ range p) :=
    ((exteriorJoukowski_differentiableOn.comp
      (slitExteriorMap_differentiableOn p h0 hH hf hb.injOn hf0)
      (slitExteriorMap_bijOn p h0 hH hs hu).mapsTo).const_mul (a:ℂ)).sub_const _
  let F := invFunOn G (upperHalfPlane \ range p)
  have ho : IsOpen (upperHalfPlane \ range p) :=
    isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed
  have hdF : DifferentiableOn ℂ F upperHalfPlane := by
    simpa only [F,hG.image_eq] using hdG.invFunOn ho hG.injOn
  have hmF : MapsTo F upperHalfPlane (upperHalfPlane \ range p) := hG.surjOn.mapsTo_invFunOn
  have hl : ∀ z ∈ upperHalfPlane \ range p, F (G z)=z := hG.injOn.leftInvOn_invFunOn
  have hr : ∀ z ∈ upperHalfPlane, G (F z)=z := hG.surjOn.rightInvOn_invFunOn
  have hnorm := slit_inverse_tendsto_ratio p h0 hH ha hf hf0 hfa hs F hl
  have hheight := normalized_inverse_height hG.mapsTo hdF
    (hmF.mono_right sdiff_subset) hl hnorm
  let c := (deriv (dslope (slitInfinityFactor f a) 0) 0).re
  have hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)) := by
    have hh := slitExteriorMap_laurent_limit (hf.analyticAt hD) hf0 ha.ne' hfa
    have he := eq_ofReal_re_of_conj_eq (derivative_real_of_reflection hD
      (dslope_reflection hD (slitInfinityFactor_reflection hD hs a)))
    rw [he] at hh
    exact hh
  have hc0 : 0≤c := by
    apply hydrodynamic_coefficient_nonneg hc
    rw [eventually_inf_principal]
    filter_upwards [(isCompact_range p.continuous).compl_mem_cocompact] with z hz
    exact fun hzH => hheight z ⟨hzH,hz⟩
  exact ⟨G,F,c,hc0,hG,hdG,hdF,hmF,hl,hr,hc,hnorm,hheight⟩

end SLEExactGauge

end

end OAI
