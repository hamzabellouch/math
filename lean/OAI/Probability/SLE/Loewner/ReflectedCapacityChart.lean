import OAI.Probability.SLE.Loewner.SlitChartUniqueness

namespace OAI

/-! Retain the reflected Riemann-map data of a normalized slit chart, so
that its analytic continuation outside the reflected slit is available
for the local evolution estimates. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

structure ReflectedCapacityChart (p : C(unitInterval,ℂ)) where
  chart : SimpleSlitChart p
  diskMap : ℂ → ℂ
  slope : ℝ
  slope_pos : 0<slope
  disk_bijOn : BijOn diskMap (invertedExterior (reflectedArcSet p)) (ball 0 1)
  disk_differentiable : DifferentiableOn ℂ diskMap (invertedExterior (reflectedArcSet p))
  disk_zero : diskMap 0=0
  disk_derivative : deriv diskMap 0=(slope:ℂ)
  disk_reflection : ∀ z∈invertedExterior (reflectedArcSet p), diskMap (conj z)=conj (diskMap z)
  forward_eq : chart.forward=slitHydrodynamicMap diskMap slope

theorem exists_reflectedCapacityChart (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane) :
    Nonempty (ReflectedCapacityChart p) := by
  obtain ⟨f,a,ha,hb,hf,hf0,hfa,hs,hu⟩ := reflected_slit_exists_normalized_chart p hi h0 hH
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have hD : invertedExterior (reflectedArcSet p)∈𝓝 (0:ℂ) :=
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
  have hl : ∀ z∈upperHalfPlane \ range p, F (G z)=z := hG.injOn.leftInvOn_invFunOn
  have hr : ∀ z∈upperHalfPlane, G (F z)=z := hG.surjOn.rightInvOn_invFunOn
  have hn := slit_inverse_tendsto_ratio p h0 hH ha hf hf0 hfa hs F hl
  have hheight := normalized_inverse_height hG.mapsTo hdF
    (hmF.mono_right sdiff_subset) hl hn
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
  have hcpos : 0<c := by
    by_contra hnot
    have hec : c=0 := le_antisymm (le_of_not_gt hnot) hc0
    have hfcoef := inverse_hydrodynamic_coefficient hc hn hr
    rw [hec,ofReal_zero,neg_zero] at hfcoef
    have hh := holomorphic_zero_hydrodynamic_mass (hdF.sub differentiableOn_id)
      (fun z hz => by
        change 0≤(F z-z).im
        simpa only [sub_im] using sub_nonneg.mpr
          (normalized_halfPlane_height hdF (hmF.mono_right sdiff_subset) hn hz)) hfcoef
    have hp1 : p 1∈upperHalfPlane := hH 1 (by norm_num)
    have hFeq : F (p 1)=p 1 := sub_eq_zero.mp (hh (p 1) hp1)
    have hmem := hmF hp1
    rw [hFeq] at hmem
    exact hmem.2 (mem_range_self 1)
  let Q : SimpleSlitChart p := ⟨G,F,c,hcpos,hG,hdG,hdF,hmF,hl,hr,hc,hn,hheight⟩
  exact ⟨⟨Q,f,a,ha,hb,hf,hf0,hfa,hs,rfl⟩⟩

end SLEExactGauge

end

end OAI
