import OAI.Probability.FreeIsing.Conditioning.NoisyBranchConditionalLaw
import OAI.Probability.FreeIsing.Gaussian.LinearSignalTilt
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorSymmetry
import OAI.Probability.FreeIsing.Spins.PosteriorTilt

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem integral_cond_spin_eq_of_ae_flip
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hflip : ∀ᵐ x ∂μ, S (T x) = (S x).flip)
    {f : Ω → ℝ} (hfm : StronglyMeasurable f) (hfi : Integrable f μ)
    (heven : ∀ᵐ x ∂μ, f (T x) = f x)
    (a : IsingSpin) (hfair : μ {x | S x = a} = (1 / 2 : ENNReal)) :
    (∫ x, f x ∂μ[|{x | S x = a}]) = ∫ x, f x ∂μ := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hsm : StronglyMeasurable (fun x => spinSign (S x)) :=
    (hsign.comp hS).stronglyMeasurable
  have hsb : ∀ᵐ x ∂μ, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    cases S x <;> norm_num [spinSign]
  have hsi : Integrable (fun x => spinSign (S x)) μ :=
    Integrable.of_bound hsm.aestronglyMeasurable 1 hsb
  have hfsi : Integrable (fun x => f x * spinSign (S x)) μ :=
    hfi.mul_bdd hsm.aestronglyMeasurable hsb
  have hzero : (∫ x, f x * spinSign (S x) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae_sign_reversal T hT
    filter_upwards [hflip, heven] with x hx hf
    rw [hf, hx]
    cases S x <;> simp [IsingSpin.flip, spinSign]
  have htilt := integral_cond_spin_posterior_tilt (mSmall := inferInstance)
    le_rfl hS hfm hfi a hfair
  have hce : μ[fun x => spinSign (S x) | (inferInstance : MeasurableSpace Ω)] =ᵐ[μ]
      fun x => spinSign (S x) := Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable le_rfl hsm hsi)
  rw [htilt]
  calc
    _ = ∫ x, f x + spinSign a * (f x * spinSign (S x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hce] with x hx
      rw [hx]
      ring
    _ = _ := by
      rw [integral_add hfi (hfsi.const_mul _), integral_const_mul, hzero]
      ring

theorem identDistrib_cond_spin_of_ae_flip
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hflip : ∀ᵐ x ∂μ, S (T x) = (S x).flip)
    {F : Ω → ℝ} (hF : Measurable F)
    (heven : ∀ᵐ x ∂μ, F (T x) = F x)
    (a : IsingSpin) (hfair : μ {x | S x = a} = (1 / 2 : ENNReal)) :
    IdentDistrib F F μ[|{x | S x = a}] μ := by
  let : IsProbabilityMeasure μ[|{x | S x = a}] :=
    cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  refine ⟨hF.aemeasurable, hF.aemeasurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hF.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_map hF.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  apply integral_cond_spin_eq_of_ae_flip T hT hS hflip
    (f.continuous.measurable.comp hF).stronglyMeasurable
    (Integrable.of_bound (f.continuous.measurable.comp hF).aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (F x)))
    _ a hfair
  filter_upwards [heven] with x hx
  exact congrArg f hx

theorem selectedPosterior_even_identDistrib_cond_spin
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r w : TreeVertex d)
    {g : ℝ → ℝ} (hg : Measurable g) (hgeven : ∀ x, g (-x) = g x)
    (s : IsingSpin) :
    IdentDistrib
      (fun p => g (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p))
      (fun p => g (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p))
      ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[|{p | p.1 w = s}])
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply identDistrib_cond_spin_of_ae_flip (plantedMarkFlipEquiv d A)
    (measurePreserving_plantedMarkFlip hμ ν hν)
    ((measurable_pi_apply w).comp measurable_fst)
    (Filter.Eventually.of_forall fun _ => rfl)
    (hg.comp (measurable_selectedPosterior _ hF v r))
    _ s (hμ.planted_spin_event_mass (fun _ => ν) w s)
  filter_upwards [selectedPosterior_flip_ae hμ ν hν hF hodd v r] with p hp
  change g (selectedPosterior _ F v r (plantedMarkFlipEquiv d A p)) = _
  change selectedPosterior _ F v r (plantedMarkFlipEquiv d A p) =
    -selectedPosterior _ F v r p at hp
  rw [hp, hgeven]
  rfl

theorem artanh_neg_unrestricted (x : ℝ) : Real.artanh (-x) = -Real.artanh x := by
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · have hn : -x ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    apply Real.tanh_injective
    rw [Real.tanh_artanh hn, Real.tanh_neg, Real.tanh_artanh hx]
  · rcases le_or_gt x (-1) with hleft | hleft
    · have hzero := Real.artanh_eq_zero_iff.mpr (Or.inl hleft)
      have hnzero := Real.artanh_eq_zero_iff.mpr
        (Or.inr (Or.inr (show 1 ≤ -x by linarith)))
      rw [hzero, hnzero, neg_zero]
    · have hright : 1 ≤ x := by
        by_contra h
        exact hx ⟨hleft, lt_of_not_ge h⟩
      have hzero := Real.artanh_eq_zero_iff.mpr (Or.inr (Or.inr hright))
      have hnzero := Real.artanh_eq_zero_iff.mpr (Or.inl (show -x ≤ -1 by linarith))
      rw [hzero, hnzero, neg_zero]

private theorem measurable_artanh_evenConditioning : Measurable Real.artanh := by
  unfold Real.artanh
  exact ((measurable_const.add measurable_id).div
    (measurable_const.sub measurable_id)).sqrt.log

theorem selectedField_abs_identDistrib_cond_spin
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p)|)
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p)|)
      ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[|{p | p.1 w = s}])
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  apply selectedPosterior_even_identDistrib_cond_spin hμ ν hν hF hodd v r w
    measurable_artanh_evenConditioning.abs _ s
  intro x
  rw [artanh_neg_unrestricted, abs_neg]

theorem HasFreeIsingLaw.selected_gaussian_field_abs_identDistrib_cond_spin
    {d : ℕ} {ι : Type*} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (t : ℝ) (variance : ℝ≥0) (v : ι → TreeVertex d)
    (r w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
        (fun a z => t * spinSign a + z) v r p)|)
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
        (fun a z => t * spinSign a + z) v r p)|)
      ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))[|{p | p.1 w = s}])
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)) := by
  apply selectedField_abs_identDistrib_cond_spin hμ (gaussianReal 0 variance)
  · simp only [gaussianReal_map_neg, neg_zero]
  · have hs : Measurable spinSign := by intro a ha; trivial
    exact ((hs.comp measurable_fst).const_mul t).add measurable_snd
  · intro a z
    cases a <;> simp [IsingSpin.flip, spinSign] <;> ring

end Problem367

end

end OAI
