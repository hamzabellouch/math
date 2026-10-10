import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoincareUnfolding

namespace OAI

/-! Positive unfolding on the actual quotient. Integrability follows from
an integrable periodization, so the seed need not have compact support. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPositive_unfold
    (f : CubicThetaPoint → ℝ) (hf : Measurable f) (hf0 : ∀ p,0≤f p)
    (g : CubicThetaQuotient → ℝ) (hg : Measurable g) (hg0 : ∀ q,0≤g q)
    (hgi : Integrable g cubicThetaQuotientMeasure)
    (hs : ∀ p,Summable (fun γ : cubicThetaPrincipalGroup => f (γ • p)))
    (he : ∀ p,(∑' γ : cubicThetaPrincipalGroup,f (γ • p))=g (cubicThetaQuotientMap p)) :
    Integrable f cubicThetaPointMeasure ∧
      (∫ p,f p ∂cubicThetaPointMeasure)=∫ q,g q ∂cubicThetaQuotientMeasure := by
  have hlin : (∫⁻ p,ENNReal.ofReal (f p) ∂cubicThetaPointMeasure)=
      ENNReal.ofReal (∫ q,g q ∂cubicThetaQuotientMeasure) := by
    calc
      _ = ∑' γ : cubicThetaPrincipalGroup,∫⁻ p in cubicThetaFundamentalDomain,
          ENNReal.ofReal (f (γ • p)) ∂cubicThetaPointMeasure :=
        (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).lintegral_eq_tsum'' _
      _ = ∫⁻ p in cubicThetaFundamentalDomain,
          ∑' γ : cubicThetaPrincipalGroup,ENNReal.ofReal (f (γ • p)) ∂cubicThetaPointMeasure := by
        rw [lintegral_tsum]
        intro γ
        exact (ENNReal.measurable_ofReal.comp (hf.comp (measurable_const_smul γ))).aemeasurable
      _ = ∫⁻ p in cubicThetaFundamentalDomain,
          ENNReal.ofReal (g (cubicThetaQuotientMap p)) ∂cubicThetaPointMeasure := by
        apply lintegral_congr
        intro p
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun γ => hf0 (γ • p)) (hs p),he p]
      _ = ∫⁻ q,ENNReal.ofReal (g q) ∂cubicThetaQuotientMeasure := by
        rw [cubicThetaQuotientMeasure]
        exact (lintegral_map (f:=fun q => ENNReal.ofReal (g q))
          (ENNReal.measurable_ofReal.comp hg)
          cubicThetaQuotientMap_open.continuous.measurable).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hgi
        (Filter.Eventually.of_forall hg0)).symm
  have hfi : Integrable f cubicThetaPointMeasure := by
    refine ⟨hf.aestronglyMeasurable,?_⟩
    change (∫⁻ p,‖f p‖ₑ ∂cubicThetaPointMeasure) < ⊤
    simp_rw [Real.enorm_of_nonneg (hf0 _)]
    rw [hlin]
    exact ENNReal.ofReal_lt_top
  refine ⟨hfi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)] at hlin
  have h := congrArg ENNReal.toReal hlin
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hf0),
    ENNReal.toReal_ofReal (integral_nonneg hg0)] using h

end CubicFirstMoment

end

end OAI
