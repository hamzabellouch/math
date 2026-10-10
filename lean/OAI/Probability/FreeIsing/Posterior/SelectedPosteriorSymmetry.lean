import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorStationarity
import OAI.Probability.FreeIsing.Posterior.Symmetry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem selectedPosterior_abs_le_one {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ∀ᵐ p ∂ρ, |selectedPosterior ρ F v r p| ≤ 1 := by
  apply ae_bdd_abs_condExp_of_ae_bdd_abs
  apply Filter.Eventually.of_forall
  intro p
  cases hs : p.1 r <;> norm_num [spinSign, hs]

theorem integrable_selectedPosterior_abs_pow {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsFiniteMeasure ρ] {F : IsingSpin → A → B}
    (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (n : ℕ) :
    Integrable (fun p => |selectedPosterior ρ F v r p| ^ n) ρ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_selectedPosterior ρ hF v r).abs.pow_const n).aestronglyMeasurable)
  filter_upwards [selectedPosterior_abs_le_one ρ F v r] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_one₀ (abs_nonneg _) hp

def plantedMarkFlipEquiv (d : ℕ) (A : Type*) [AddGroup A]
    [MeasurableSpace A] [MeasurableNeg A] :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) ≃ᵐ
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) where
  toFun := Prod.map flipConfig Neg.neg
  invFun := Prod.map flipConfig Neg.neg
  left_inv := by rintro ⟨σ, z⟩; change (flipConfig (flipConfig σ), - -z) = (σ, z); simp
  right_inv := by rintro ⟨σ, z⟩; change (flipConfig (flipConfig σ), - -z) = (σ, z); simp
  measurable_toFun := measurable_flipConfig.prodMap measurable_neg
  measurable_invFun := measurable_flipConfig.prodMap measurable_neg

theorem measurePreserving_plantedMarkFlip {d : ℕ} {A : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν) :
    MeasurePreserving (plantedMarkFlipEquiv d A)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  have hm : (Measure.infinitePi (fun _ : TreeVertex d => ν)).map Neg.neg =
      Measure.infinitePi (fun _ : TreeVertex d => ν) := by
    change (Measure.infinitePi (fun _ : TreeVertex d => ν)).map
      (fun z i => -z i) = _
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_neg)]
    simp only [hν]
  exact (show MeasurePreserving flipConfig μ μ from
    ⟨measurable_flipConfig, hμ.flip_invariant⟩).prod
    (show MeasurePreserving Neg.neg
      (Measure.infinitePi (fun _ : TreeVertex d => ν))
      (Measure.infinitePi (fun _ : TreeVertex d => ν)) from ⟨measurable_neg, hm⟩)

theorem measurable_plantedMarkFlip_selectedObservationField
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B]
    (F : IsingSpin → A → B)
    (hodd : ∀ s z, F s.flip (-z) = -F s z) (v : ι → TreeVertex d) :
    Measurable[selectedObservationField F v, selectedObservationField F v]
      (plantedMarkFlipEquiv d A) := by
  apply measurable_comap_iff.mpr
  have heq : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun i => F (p.1 (v i)) (p.2 (v i))) ∘ plantedMarkFlipEquiv d A =
      fun p i => -F (p.1 (v i)) (p.2 (v i)) := by
    funext p i
    exact hodd (p.1 (v i)) (p.2 (v i))
  rw [heq]
  exact (comap_measurable (fun p : (TreeVertex d → IsingSpin) ×
    (TreeVertex d → A) => fun i => F (p.1 (v i)) (p.2 (v i)))).neg

theorem selectedPosterior_flip_ae {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r ∘
      plantedMarkFlipEquiv d A =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      -selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r := by
  let := hμ.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ρ := by
    have hs : Measurable spinSign := by intro s hs; trivial
    apply Integrable.of_bound
      ((hs.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hm := measurable_plantedMarkFlip_selectedObservationField F hodd v
  have hn := condExp_comp_measurePreserving_equiv
    (selectedObservationField_le hF v) (plantedMarkFlipEquiv d A)
    (measurePreserving_plantedMarkFlip hμ ν hν) hm hm hi
  have ho : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ∘ plantedMarkFlipEquiv d A =
      -(fun p => spinSign (p.1 r)) := by
    funext p
    cases hs : p.1 r <;>
      simp [plantedMarkFlipEquiv, flipConfig, IsingSpin.flip, spinSign, hs]
  rw [ho] at hn
  exact hn.trans (condExp_neg _ _)

theorem selectedPosteriorLaw_neg_invariant {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map
      (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r)).map
        Neg.neg =
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map
        (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_plantedMarkFlip hμ ν hν) measurable_neg
    (measurable_selectedPosterior _ hF v r)
    (selectedPosterior_flip_ae hμ ν hν hF hodd v r)

theorem HasFreeIsingLaw.selected_gaussian_posteriorLaw_neg_invariant
    {d : ℕ} {ι : Type*} {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (t : ℝ) (variance : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
      (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
        (fun s z => t * spinSign s + z) v r)).map Neg.neg =
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
        (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
          (fun s z => t * spinSign s + z) v r) := by
  apply selectedPosteriorLaw_neg_invariant hμ (gaussianReal 0 variance)
  · simp only [gaussianReal_map_neg, neg_zero]
  · have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul t).add measurable_snd
  · intro s z
    cases s <;> simp [IsingSpin.flip, spinSign] <;> ring

end Problem367

end

end OAI
