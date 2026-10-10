import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCover
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientMeasure

namespace OAI

/-! Finite-index integral transport in the fixed arithmetic action,
including the nonintegrable case of the Bochner integral convention. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

variable (D : CubicThetaArithmeticCover) (K : Subgroup cubicThetaPrincipalGroup)
  (hle : K≤D.group) [K.FiniteIndex]

omit [K.FiniteIndex] in
lemma cubicThetaRelativeDomain_disjoint :
    Pairwise (fun t u : cubicThetaRelativeTransversal D K =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' D.domain)
        ((fun x : CubicThetaPoint => u.val • x) '' D.domain)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  dsimp only at hga hgb
  have hm : (u.val⁻¹*t.val) • a=b := by rw [mul_smul,hga,←hgb,inv_smul_smul]
  have he : u.val⁻¹*t.val=1 := (D.unique a).unique
    (by rwa [hm]) (by simpa using ha)
  exact htu (Subtype.ext (inv_mul_eq_one.mp he).symm)

section Integral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cubicThetaRelativeDomain_integral {f : CubicThetaPoint → E}
    (hi : ∀ (g : D.group) x, f (g • x)=f x) :
    (∫ x in cubicThetaRelativeDomain D K, f x ∂cubicThetaPointMeasure)=
      ((cubicThetaRelativeSubgroup D K).index:ℝ) •
        ∫ x in D.domain, f x ∂cubicThetaPointMeasure := by
  classical
  let : Fintype (cubicThetaRelativeTransversal D K) := Fintype.ofFinite _
  have hmeas (t : cubicThetaRelativeTransversal D K) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' D.domain) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image' D.measurable
  by_cases hf : IntegrableOn f D.domain cubicThetaPointMeasure
  · have hint (t : cubicThetaRelativeTransversal D K) :
        IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' D.domain)
          cubicThetaPointMeasure := by
      apply ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
        (measurableEmbedding_const_smul t.val)).mpr
      simpa only [Function.comp_def,hi] using hf
    change (∫ x in ⋃ t : cubicThetaRelativeTransversal D K,
      (fun y : CubicThetaPoint => t.val • y) '' D.domain, f x
        ∂cubicThetaPointMeasure)=_
    rw [integral_iUnion_fintype hmeas (cubicThetaRelativeDomain_disjoint D K) hint]
    have ht (t : cubicThetaRelativeTransversal D K) :
        (∫ x in (fun y : CubicThetaPoint => t.val • y) '' D.domain,
          f x ∂cubicThetaPointMeasure)=∫ x in D.domain, f x ∂cubicThetaPointMeasure := by
      rw [(measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
        (measurableEmbedding_const_smul t.val) f D.domain]
      simp only [hi]
    simp only [ht,Finset.sum_const,Finset.card_univ]
    rw [←Nat.card_eq_fintype_card,(cubicThetaRelativeTransversal_complement D K).card_right,
      Nat.cast_smul_eq_nsmul ℝ]
  · have hnot : ¬IntegrableOn f (cubicThetaRelativeDomain D K) cubicThetaPointMeasure := by
      intro hrel
      obtain ⟨⟨h,t⟩,_⟩ := (cubicThetaRelativeTransversal_complement D K).existsUnique (1:D.group)
      have hsub : ((fun x : CubicThetaPoint => t.val • x) '' D.domain)⊆
          cubicThetaRelativeDomain D K := by
        exact subset_iUnion (fun u : cubicThetaRelativeTransversal D K =>
          (fun x : CubicThetaPoint => u.val • x) '' D.domain) t
      have hint := hrel.mono_set hsub
      have hint' := ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
        (measurableEmbedding_const_smul t.val)).mp hint
      apply hf
      simpa only [Function.comp_def,hi] using hint'
    rw [integral_undef hnot,integral_undef hf,smul_zero]

include hle in
theorem cubicThetaFiniteCover_integral (S : Set CubicThetaPoint)
    (hS : IsFundamentalDomain K S cubicThetaPointMeasure) {f : CubicThetaPoint → E}
    (hi : ∀ (g : D.group) x, f (g • x)=f x) :
    (∫ x in S, f x ∂cubicThetaPointMeasure)=
      ((cubicThetaRelativeSubgroup D K).index:ℝ) •
        ∫ x in D.domain, f x ∂cubicThetaPointMeasure := by
  have hk (g : K) (x : CubicThetaPoint) : f (g • x)=f x := hi ⟨g.val,hle g.property⟩ x
  rw [hS.setIntegral_eq ((cubicThetaRelativeCover D K hle).fundamental cubicThetaPointMeasure) hk]
  exact cubicThetaRelativeDomain_integral D K hi

end Integral
end CubicFirstMoment

end

end OAI
