import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1GradientLinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaChartRestrictedIntegral

namespace OAI

/-! The sesquilinear differential pairing descends to the arithmetic
quotient; its value is independent of the measurable frame choice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Gradient_norm_invariant (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    ‖cubicThetaSectionGradient F (g • p)‖=‖cubicThetaSectionGradient F p‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaSectionGradient_norm_sq,cubicThetaSectionGradient_norm_sq]
  exact cubicThetaC1Energy_invariant F hF g p

lemma cubicThetaC1Gradient_inner_invariant (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    inner ℂ (cubicThetaSectionGradient F (g • p)) (cubicThetaSectionGradient G (g • p))=
      inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p) := by
  have hsum := cubicThetaC1Gradient_norm_invariant (F+G) (hF.add hG) g p
  have hsub := cubicThetaC1Gradient_norm_invariant (F-G) (hF.sub hG) g p
  have hsumI := cubicThetaC1Gradient_norm_invariant (F+Complex.I • G) (hF.add (hG.const_smul Complex.I)) g p
  have hsubI := cubicThetaC1Gradient_norm_invariant (F-Complex.I • G) (hF.sub (hG.const_smul Complex.I)) g p
  simp only [cubicThetaC1Gradient_add _ _ hF hG] at hsum
  simp only [cubicThetaC1Gradient_sub _ _ hF hG] at hsub
  simp only [cubicThetaC1Gradient_add F (Complex.I • G) hF (hG.const_smul Complex.I),
    cubicThetaC1Gradient_smul Complex.I G hG] at hsumI
  simp only [cubicThetaC1Gradient_sub F (Complex.I • G) hF (hG.const_smul Complex.I),
    cubicThetaC1Gradient_smul Complex.I G hG] at hsubI
  rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
  change ((‖cubicThetaSectionGradient F (g • p)+cubicThetaSectionGradient G (g • p)‖:ℂ)^2-
    (‖cubicThetaSectionGradient F (g • p)-cubicThetaSectionGradient G (g • p)‖:ℂ)^2+
    ((‖cubicThetaSectionGradient F (g • p)-Complex.I • cubicThetaSectionGradient G (g • p)‖:ℂ)^2-
    (‖cubicThetaSectionGradient F (g • p)+Complex.I • cubicThetaSectionGradient G (g • p)‖:ℂ)^2)*Complex.I)/4=_
  rw [hsum,hsub,hsubI,hsumI]
  rfl

def cubicThetaC1Pairing (F G : CubicThetaSection) (q : CubicThetaQuotient) : ℂ :=
  inner ℂ (cubicThetaSectionGradient F (cubicThetaQuotientLift q))
    (cubicThetaSectionGradient G (cubicThetaQuotientLift q))

lemma cubicThetaC1Pairing_apply (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    cubicThetaC1Pairing F G (cubicThetaQuotientMap p)=
      inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p) := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaC1Pairing
  rw [← hg,cubicThetaC1Gradient_inner_invariant F G hF hG]

lemma cubicThetaC1Pairing_continuous (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaC1Pairing F G) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaC1Pairing F G ∘ cubicThetaQuotientMap=
      fun p => inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p) :=
    funext (cubicThetaC1Pairing_apply F G hF hG)
  rw [he]
  exact (cubicThetaC1Gradient_continuous F hF).inner (cubicThetaC1Gradient_continuous G hG)

lemma cubicThetaC1Pairing_representative (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (q : CubicThetaQuotient) :
    cubicThetaC1Pairing F G q=inner ℂ (cubicThetaGradientRepresentative F q)
      (cubicThetaGradientRepresentative G q) := by
  have h := cubicThetaC1Pairing_apply F G hF hG (cubicThetaBorelSection q)
  rwa [cubicThetaBorelSection_rightInverse] at h

lemma cubicThetaChart_complex_integral
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (f : CubicThetaQuotient → ℂ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaChart_map_restrict e he hS hSe]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

end CubicFirstMoment

end

end OAI
