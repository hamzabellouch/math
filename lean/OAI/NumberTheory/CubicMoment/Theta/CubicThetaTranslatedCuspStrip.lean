import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripEnergy

namespace OAI

/-! Every arithmetic cusp strip remains injective after an integral
Mobius transformation. Normality of the actual level-three group and
invariance of hyperbolic measure give the exact transported integrals. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrincipalConjugate (δ : SL(2,Eisenstein)) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrincipalGroup :=
  ⟨δ⁻¹*g.val*δ,by
    let ρ : SL(2,Eisenstein) →* SL(2,Residues (3:Eisenstein)) :=
      Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))
    change ρ (δ⁻¹*g.val*δ)=1
    have hg : ρ g.val=1 := g.property
    rw [map_mul,map_mul,map_inv,hg,mul_one,inv_mul_cancel]⟩

def cubicThetaTranslatedCuspStrip (δ : SL(2,Eisenstein)) (H : ℝ) : Set CubicThetaPoint :=
  (fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H

lemma cubicThetaTranslatedCuspStrip_measurable (δ : SL(2,Eisenstein)) (H : ℝ) :
    MeasurableSet (cubicThetaTranslatedCuspStrip δ H) :=
  (Homeomorph.smul δ).measurableEmbedding.measurableSet_image' (cubicThetaCuspStrip_measurable H)

lemma cubicThetaTranslatedCuspStrip_injective (δ : SL(2,Eisenstein))
    {H : ℝ} (hH : 1≤H) : InjOn cubicThetaQuotientMap (cubicThetaTranslatedCuspStrip δ H) := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ he
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change g.val • (δ • q)=δ • p at hg
  have hc : cubicThetaPrincipalConjugate δ g • q=p := by
    change (δ⁻¹*g.val*δ) • q=p
    rw [mul_smul,mul_smul,hg,inv_smul_smul]
  have hπ : cubicThetaQuotientMap p=cubicThetaQuotientMap q := by
    rw [← hc,cubicThetaQuotient_covering.map_smul]
  exact congrArg (fun r : CubicThetaPoint => δ • r) (cubicThetaCuspStrip_injective hH hp hq hπ)

lemma cubicThetaSmul_map_restrict (δ : SL(2,Eisenstein)) {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map (fun p : CubicThetaPoint => δ • p)=
      cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' S) := by
  have hImage := (Homeomorph.smul δ).measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((fun p : CubicThetaPoint => δ • p) '' S) at hImage
  have h := Measure.restrict_map (measurable_const_smul δ) hImage (μ:=cubicThetaPointMeasure)
  rw [(measurePreserving_smul δ cubicThetaPointMeasure).map_eq] at h
  have he : (fun p : CubicThetaPoint => δ • p) ⁻¹' ((fun p : CubicThetaPoint => δ • p) '' S)=S :=
    Set.preimage_image_eq _ (MulAction.injective δ)
  rw [he] at h
  exact h.symm

lemma cubicThetaTranslatedCuspStrip_integral (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H)
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' cubicThetaTranslatedCuspStrip δ H,
      f q ∂cubicThetaQuotientMeasure)=
      ∫ p in cubicThetaCuspStrip H, f (cubicThetaQuotientMap (δ • p)) ∂cubicThetaPointMeasure := by
  rw [cubicThetaInjective_integral (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH) f hf]
  change (∫ p, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure.restrict
    ((fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H))=_
  rw [← cubicThetaSmul_map_restrict δ (cubicThetaCuspStrip_measurable H)]
  exact integral_map_of_stronglyMeasurable (measurable_const_smul δ)
    (hf.comp_measurable cubicThetaQuotientMap_open.continuous.measurable)

lemma cubicThetaTranslatedCuspStrip_integrable (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure) :
    IntegrableOn (fun p => f (cubicThetaQuotientMap (δ • p))) (cubicThetaCuspStrip H)
      cubicThetaPointMeasure := by
  have h := hf.integrableOn (s:=cubicThetaQuotientMap '' cubicThetaTranslatedCuspStrip δ H)
  unfold IntegrableOn at h
  rw [← cubicThetaInjective_map_restrict (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH)] at h
  have hi := h.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  change Integrable (fun p => f (cubicThetaQuotientMap p))
    (cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H)) at hi
  rw [← cubicThetaSmul_map_restrict δ (cubicThetaCuspStrip_measurable H)] at hi
  simpa only [IntegrableOn,Function.comp_def] using
    hi.comp_measurable (measurable_const_smul δ)

end CubicFirstMoment

end

end OAI
