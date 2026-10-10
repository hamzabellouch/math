import OAI.Probability.SLE.Geometry.ReciprocalInverseLimit

namespace OAI

/-! Identification of the analytic inverse germ with the physical slit
inverse for all sufficiently large points of the half-plane. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma slitHydrodynamicMap_conjugateInversion
    {D : Set ℂ} (hD : D ∈ 𝓝 (0:ℂ)) {f : ℂ → ℂ} (hf0 : f 0=0)
    (hs : ∀ z ∈ D, f (conj z)=conj (f z)) (a : ℝ)
    {x : ℂ} (hx : x ∈ D) (hx0 : x ≠ 0) :
    slitHydrodynamicMap f a (conjugateInversion x)=
      conjugateInversion (slitReciprocalMap f a x) := by
  have hh := slitReciprocalMap_identity hf0 a (conjugateInversion_ne_zero hx0)
  have hq := slitReciprocalMap_reflection hD hs a x hx
  simp only [conjugateInversion,inv_inv] at hh
  rw [hq] at hh
  exact hh.symm

theorem slit_inverse_tendsto_ratio
    (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {f : ℂ → ℂ} {a : ℝ} (ha : 0<a)
    (hf : DifferentiableOn ℂ f (invertedExterior (reflectedArcSet p)))
    (hf0 : f 0=0) (hfa : deriv f 0=(a:ℂ))
    (hs : ∀ z ∈ invertedExterior (reflectedArcSet p), f (conj z)=conj (f z))
    (F : ℂ → ℂ)
    (hleft : ∀ z ∈ upperHalfPlane \ range p, F (slitHydrodynamicMap f a z)=z) :
    Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have hD : invertedExterior (reflectedArcSet p) ∈ 𝓝 (0:ℂ) :=
    (invertedExterior_isOpen hK).mem_nhds (zero_mem_invertedExterior _)
  obtain ⟨r,ε,hε,hr,hr0,hrd,hupper,hl,hh⟩ :=
    slitReciprocalMap_exists_upper_inverse hD (hf.analyticAt hD) ha.ne' hfa hs
  have hrT : Tendsto r (𝓝 (0:ℂ)) (𝓝 0) := by simpa only [hr0] using hr.continuousAt.tendsto
  have hM := conjugateInversion_tendsto_zero
  have hrD := (hrT.comp hM).eventually hD
  have heq := hM.eventually hh
  have hsmall := hM.eventually (ball_mem_nhds (0:ℂ) hε)
  have hMb := conjugateInversion_slit_bijOn p h0 hH
  have he : (fun z : ℂ => F z/z) =ᶠ[cocompact ℂ ⊓ 𝓟 upperHalfPlane]
      (fun z => conjugateInversion (r (conjugateInversion z))/z) := by
    change ∀ᶠ z in cocompact ℂ ⊓ 𝓟 upperHalfPlane,
      F z/z=conjugateInversion (r (conjugateInversion z))/z
    rw [eventually_inf_principal]
    filter_upwards [hrD,heq,hsmall] with z hzD hzq hzb
    intro hzH
    have hzD' : r (conjugateInversion z) ∈ invertedExterior (reflectedArcSet p) := by
      simpa only [Function.comp_apply,invertedExterior,mem_ofPred_eq] using hzD
    have hMz := conjugateInversion_upper hzH
    have hrH := hupper ⟨hzb,hMz⟩
    have hrne : r (conjugateInversion z) ≠ 0 := by
      intro hzero
      have hi := congrArg Complex.im hzero
      simp only [zero_im] at hi
      exact hrH.ne' hi
    have hx : conjugateInversion (r (conjugateInversion z)) ∈ upperHalfPlane \ range p := by
      obtain ⟨v,hv,hvr⟩ := hMb.surjOn ⟨hzD',hrH⟩
      have he : v=conjugateInversion (r (conjugateInversion z)) := by
        rw [← hvr,conjugateInversion_involutive]
      exact he ▸ hv
    have hG := slitHydrodynamicMap_conjugateInversion hD hf0 hs a hzD' hrne
    rw [hzq,conjugateInversion_involutive] at hG
    have hF := hleft _ hx
    rw [hG] at hF
    rw [hF]
  have ht := (reciprocal_inverse_tendsto_ratio
    (by simpa only [hrd] using hr.differentiableAt.hasDerivAt) hr0).mono_left
      (show cocompact ℂ ⊓ 𝓟 upperHalfPlane ≤ cocompact ℂ from inf_le_left)
  exact ht.congr' he.symm

end SLEExactGauge

end

end OAI
