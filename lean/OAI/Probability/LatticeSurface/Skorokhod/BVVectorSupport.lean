import Mathlib

namespace OAI

noncomputable section

open Set Filter MeasureTheory MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ConvexSkorokhod

theorem exists_continuous_bv_vector_measure
    {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [CompactIccSpace α] [hα : MeasurableSpace α] [BorelSpace α]
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (f : α → E)
    (hf : BoundedVariationOn f univ) (hc : Continuous f) (x₀ : α) :
    ∃ μ : VectorMeasure α E, IsFiniteMeasure μ.variation ∧
      μ botSet=0 ∧ ∀ a b,a ≤ b → μ (Ioc a b)=f b-f a := by
  let : Nonempty α := ⟨x₀⟩
  let ρ := (hf.stieltjesFunctionRightLim x₀).measure
  have : IsFiniteMeasure ρ := by
    apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
      (C := (eVariationOn f.rightLim univ).toReal) _ (fun x ↦ ?_)
    exact variationOnFromTo.abs_le_eVariationOn hf.rightLim
  let m := AddContent.onIoc f.rightLim
  have A : ∀ s ∈ {s | ∃ a b,a ≤ b ∧ s=Ioc a b},‖m s‖ₑ ≤ ρ s := by
    rintro s ⟨a,b,hab,rfl⟩
    rw [AddContent.onIoc_apply hab]
    simp only [ρ,StieltjesFunction.measure_Ioc,BoundedVariationOn.stieltjesFunctionRightLim_apply]
    rw [←variationOnFromTo.add hf.rightLim.locallyBoundedVariationOn (mem_univ x₀) (mem_univ a) (mem_univ b)]
    simp only [add_sub_cancel_left,variationOnFromTo,hab,↓reduceIte,univ_inter]
    rw [ENNReal.ofReal_toReal];swap
    · exact ((eVariationOn.mono _ (subset_univ _)).trans_lt hf.rightLim.lt_top).ne
    rw [←edist_eq_enorm_sub]
    exact eVariationOn.edist_le _ (by grind) (by grind)
  have hgen : hα=generateFrom {s | ∃ a b,a ≤ b ∧ s=Ioc a b} := by
    borelize α
    convert! borel_eq_generateFrom_Ioc_le α using 2
    grind only
  obtain ⟨μ,hμ,hbound⟩ := VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    IsSetSemiring.Ioc A hgen
  have hvle : μ.variation ≤ ρ := VectorMeasure.variation_le_of_forall_enorm_le (fun s _ => hbound s)
  refine ⟨μ,isFiniteMeasure_of_le _ hvle,?_,?_⟩
  · apply enorm_eq_zero.mp
    apply le_bot_iff.mp
    exact (hbound botSet).trans (by simp [ρ])
  · intro a b hab
    rw [hμ _ ⟨a,b,hab,rfl⟩,AddContent.onIoc_apply hab,
      hc.continuousAt.continuousWithinAt.rightLim_eq,
      hc.continuousAt.continuousWithinAt.rightLim_eq]

end ConvexSkorokhod

end

end OAI
