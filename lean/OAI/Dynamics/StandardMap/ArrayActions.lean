import OAI.Dynamics.StandardMap.CriticalLimits

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTranslate_mem_affine_iff (r : DyadicTime) (d : DistanceArray) :
    arrayTranslate r d ∈ affineLocus ↔ d ∈ affineLocus := by
  constructor
  · rintro ⟨w,hw⟩
    have hh := congrArg (arrayTranslate (-r)) hw
    rw [arrayTranslate_affine,arrayTranslate_add,neg_add_cancel,arrayTranslate_zero] at hh
    exact ⟨w,hh⟩
  · rintro ⟨w,rfl⟩; exact ⟨w,(arrayTranslate_affine r w).symm⟩
noncomputable def nonaffineTranslation (r : DyadicTime) : NonAffineArray ≃ₜ NonAffineArray where
  toFun d := ⟨arrayTranslate r d.val,by simpa only [arrayTranslate_mem_affine_iff] using d.property⟩
  invFun d := ⟨arrayTranslate (-r) d.val,by simpa only [arrayTranslate_mem_affine_iff] using d.property⟩
  left_inv d := by apply Subtype.ext; exact (arrayTranslation r).left_inv d.val
  right_inv d := by apply Subtype.ext; exact (arrayTranslation r).right_inv d.val
  continuous_toFun := (continuous_arrayTranslate r).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (continuous_arrayTranslate (-r)).comp continuous_subtype_val |>.subtype_mk _
noncomputable def nonaffineDilate (d : NonAffineArray) : NonAffineArray :=
  ⟨arrayDilate d.val,by simpa only [arrayDilate_mem_affine_iff] using d.property⟩
lemma continuous_nonaffineDilate : Continuous nonaffineDilate :=
  (continuous_arrayDilate.comp continuous_subtype_val).subtype_mk _
lemma proper_nonaffineDilate : IsProperMap nonaffineDilate := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_nonaffineDilate,?_⟩
  intro K hK
  have hA : IsCompact (Subtype.val '' K : Set DistanceArray) := hK.image continuous_subtype_val
  have hB : IsCompact (arrayDilate ⁻¹' (Subtype.val '' K)) :=
    (hA.isClosed.preimage continuous_arrayDilate).isCompact
  have hsub : arrayDilate ⁻¹' (Subtype.val '' K) ⊆ affineLocusᶜ := by
    rintro d ⟨u,hu,he⟩
    exact fun hd => u.property (he ▸ (arrayDilate_mem_affine_iff d).mpr hd)
  have hsub' : arrayDilate ⁻¹' (Subtype.val '' K) ⊆ Set.range ((↑) : NonAffineArray → DistanceArray) :=
    fun d hd => ⟨⟨d,hsub hd⟩,rfl⟩
  have hh := IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hB hsub'
  convert! hh using 1
  ext d
  change nonaffineDilate d ∈ K ↔ ∃ u ∈ K,u.val=arrayDilate d.val
  exact ⟨fun hd => ⟨nonaffineDilate d,hd,rfl⟩,fun ⟨u,hu,he⟩ => (Subtype.ext he : u=nonaffineDilate d) ▸ hu⟩
noncomputable def nonaffineDilation : CocompactMap NonAffineArray NonAffineArray where
  toFun := nonaffineDilate
  continuous_toFun := continuous_nonaffineDilate
  cocompact_tendsto' := (isProperMap_iff_tendsto_cocompact.mp proper_nonaffineDilate).2

noncomputable def arrayTestExtend (g : C_c(NonAffineArray,ℝ)) : C_c(DistanceArray,ℝ) := {
  toFun := Subtype.val.extend g 0
  continuous_toFun := HasCompactSupport.continuous_extend_zero isClosed_affineLocus.isOpen_compl g.continuous g.hasCompactSupport
  hasCompactSupport' := g.hasCompactSupport.extend_zero continuous_subtype_val }
@[simp] lemma arrayTestExtend_apply (g : C_c(NonAffineArray,ℝ)) (d : NonAffineArray) :
    arrayTestExtend g d.val=g d := Subtype.val_injective.extend_apply _ _ _
lemma arrayTestExtend_affine (g : C_c(NonAffineArray,ℝ)) (d : DistanceArray) (hd : d∈affineLocus) :
    arrayTestExtend g d=0 := by
  apply Function.extend_apply' _ _ _
  rintro ⟨u,rfl⟩
  exact u.property hd
lemma integral_arrayTestExtend (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (g : C_c(NonAffineArray,ℝ)) : (∫ d,arrayTestExtend g d ∂μ)=∫ d,g d ∂nonaffinePart μ := by
  have he : (∫ d,g d ∂nonaffinePart μ)=∫ d in affineLocusᶜ,arrayTestExtend g d ∂μ := by
    convert! integral_subtype_comap isClosed_affineLocus.isOpen_compl.measurableSet (arrayTestExtend g) using 1
    simp only [arrayTestExtend_apply]
    rfl
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro d hd
  exact arrayTestExtend_affine g d (not_not.mp hd)
end StandardMapEntropy

end OAI
