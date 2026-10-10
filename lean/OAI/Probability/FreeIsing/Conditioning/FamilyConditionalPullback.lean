import OAI.Probability.FreeIsing.Conditioning.Pullback

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iCondIndepFun_comp_measurePreserving
    {Ω Ω' ι : Type*} {C : ι → Type*}
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [mC : ∀ i, MeasurableSpace (C i)]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : ∀ i, Ω' → C i} (hf : ∀ i, @Measurable Ω' (C i) mΩ' (mC i) (f i))
    (hfamily : iCondIndepFun m hm f ν) :
    iCondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (fun i => f i ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC (fun i => f i ∘ e)
    (fun i => (hf i).comp he.measurable)]
  intro S sets hsets
  let E : Set Ω' := ⋂ i ∈ S, f i ⁻¹' sets i
  have hE : MeasurableSet E :=
    S.measurableSet_biInter (fun i hi => (hsets i hi).preimage (hf i))
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have heach : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      μ[((f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ))) ∘ e | m.comap e] ω =
        ν[(f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ)) | m] (e ω) := by
    apply S.eventually_all.mpr
    intro i hi
    exact condExp_comp_measurePreserving μ ν e he m hm
      ((integrable_const (1 : ℝ)).indicator ((hsets i hi).preimage (hf i)))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC f hf).mp hfamily S hsets)
  filter_upwards [hCE, heach, hmul] with ω hωE hωeach hωmul
  simp only [Finset.prod_apply, Function.comp_apply] at hωmul ⊢
  have hindicator : (⋂ i ∈ S, (f i ∘ e) ⁻¹' sets i).indicator
      (fun _ => (1 : ℝ)) = (E.indicator (fun _ => (1 : ℝ))) ∘ e := by
    funext x
    simp [E, Set.indicator, Function.comp_def]
  rw [hindicator]
  exact hωE.trans (hωmul.trans (Finset.prod_congr rfl (fun i hi => (hωeach i hi).symm)))

theorem iCondIndepFun_iff_comp_measurePreserving
    {Ω Ω' ι : Type*} {C : ι → Type*}
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [mC : ∀ i, MeasurableSpace (C i)]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : ∀ i, Ω' → C i} (hf : ∀ i, @Measurable Ω' (C i) mΩ' (mC i) (f i)) :
    iCondIndepFun m hm f ν ↔
      iCondIndepFun (m.comap e)
        ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
          (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
        (fun i => f i ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  refine ⟨iCondIndepFun_comp_measurePreserving μ ν e he m hm hf, ?_⟩
  intro hsource
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC f hf]
  intro S sets hsets
  have hmCE (h : Ω' → ℝ) : Measurable (ν[h | m]) :=
    (stronglyMeasurable_condExp.mono hm).measurable
  apply (ae_eq_iff_comp_measurePreserving μ ν e he (hmCE _) ?_).mpr
  swap
  · convert S.measurable_prod (fun i hi =>
      hmCE ((f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ)))) using 1
    ext ω'
    simp only [Finset.prod_apply]
  let E : Set Ω' := ⋂ i ∈ S, f i ⁻¹' sets i
  have hE : MeasurableSet E :=
    S.measurableSet_biInter (fun i hi => (hsets i hi).preimage (hf i))
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have heach : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      μ[((f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ))) ∘ e | m.comap e] ω =
        ν[(f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ)) | m] (e ω) := by
    apply S.eventually_all.mpr
    intro i hi
    exact condExp_comp_measurePreserving μ ν e he m hm
      ((integrable_const (1 : ℝ)).indicator ((hsets i hi).preimage (hf i)))
  have hmul := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC
    (fun i => f i ∘ e) (fun i => (hf i).comp he.measurable)).mp hsource S hsets
  filter_upwards [hCE, heach, hmul] with ω hωE hωeach hωmul
  have hindicator : (⋂ i ∈ S, (f i ∘ e) ⁻¹' sets i).indicator
      (fun _ => (1 : ℝ)) = (E.indicator (fun _ => (1 : ℝ))) ∘ e := by
    funext x
    simp [E, Set.indicator, Function.comp_def]
  rw [hindicator] at hωmul
  simp only [Function.comp_apply, Finset.prod_apply] at hωmul ⊢
  exact hωE.symm.trans (hωmul.trans (Finset.prod_congr rfl (fun i hi => hωeach i hi)))

alias ⟨_, iCondIndepFun_of_comp_measurePreserving⟩ :=
  iCondIndepFun_iff_comp_measurePreserving

end Problem367

end

end OAI
