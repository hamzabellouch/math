import OAI.Probability.SLE.Geometry.NormalizedReflectedSlit
import OAI.Probability.SLE.Geometry.ConjugateInversionChart

namespace OAI

/-! The normalized reflected Riemann chart gives an analytic chart from
an arbitrary simple attached slit domain onto the upper exterior disk. -/
noncomputable section
open Set Complex Function Metric
open scoped ComplexConjugate

namespace SLEExactGauge

def slitExteriorMap (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z⁻¹)⁻¹

lemma inverse_mem_reflected_inverted
    (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlane \ range p) :
    z⁻¹ ∈ invertedExterior (reflectedArcSet p) := by
  have hm := (conjugateInversion_slit_bijOn p h0 hH).mapsTo hz
  have hc := invertedExterior_conj (reflectedArcSet_conj p) hm.1
  simpa only [conjugateInversion,map_inv₀,conj_conj] using hc

lemma slitExteriorMap_eq_conjugate
    (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {f : ℂ → ℂ}
    (hs : ∀ z ∈ invertedExterior (reflectedArcSet p), f (conj z)=conj (f z)) :
    EqOn (conjugateInversion ∘ f ∘ conjugateInversion) (slitExteriorMap f)
      (upperHalfPlane \ range p) := by
  intro z hz
  have he := hs z⁻¹ (inverse_mem_reflected_inverted p h0 hH hz)
  change (conj (f ((conj z)⁻¹)))⁻¹ = (f z⁻¹)⁻¹
  rw [← map_inv₀ conj z,he,conj_conj]

lemma slitExteriorMap_bijOn
    (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {f : ℂ → ℂ}
    (hs : ∀ z ∈ invertedExterior (reflectedArcSet p), f (conj z)=conj (f z))
    (hb : BijOn f (invertedExterior (reflectedArcSet p) ∩ upperHalfPlane)
      (ball 0 1 ∩ upperHalfPlane)) :
    BijOn (slitExteriorMap f) (upperHalfPlane \ range p) exteriorUpperDisk := by
  exact ((conjugateInversion_disk_upper_bijOn.comp hb).comp
    (conjugateInversion_slit_bijOn p h0 hH)).congr
      (slitExteriorMap_eq_conjugate p h0 hH hs)

lemma slitExteriorMap_differentiableOn
    (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (invertedExterior (reflectedArcSet p)))
    (hi : InjOn f (invertedExterior (reflectedArcSet p))) (hf0 : f 0=0) :
    DifferentiableOn ℂ (slitExteriorMap f) (upperHalfPlane \ range p) := by
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  intro z hz
  have hz0 : z ≠ 0 := by
    intro he
    have hzH := hz.1
    simp only [upperHalfPlane,mem_ofPred_eq,he,zero_im,lt_self_iff_false] at hzH
  have hm := inverse_mem_reflected_inverted p h0 hH hz
  have hdf := hf.differentiableAt ((invertedExterior_isOpen hK).mem_nhds hm)
  have hfi : f z⁻¹ ≠ 0 := by
    intro he
    have heq := hi hm (zero_mem_invertedExterior _) (he.trans hf0.symm)
    exact inv_ne_zero hz0 heq
  exact ((hdf.comp z (differentiableAt_id.inv hz0)).inv hfi).differentiableWithinAt

theorem simple_slit_exists_exterior_chart
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ (f : ℂ → ℂ) (a : ℝ), 0 < a ∧
      BijOn (slitExteriorMap f) (upperHalfPlane \ range p) exteriorUpperDisk ∧
      DifferentiableOn ℂ (slitExteriorMap f) (upperHalfPlane \ range p) ∧
      f 0=0 ∧ deriv f 0=(a:ℂ) ∧
      DifferentiableOn ℂ f (invertedExterior (reflectedArcSet p)) := by
  obtain ⟨f,a,ha,hb,hf,hf0,hfa,hs,hu⟩ :=
    reflected_slit_exists_normalized_chart p hi h0 hH
  exact ⟨f,a,ha,slitExteriorMap_bijOn p h0 hH hs hu,
    slitExteriorMap_differentiableOn p h0 hH hf hb.injOn hf0,hf0,hfa,hf⟩

end SLEExactGauge

end

end OAI
