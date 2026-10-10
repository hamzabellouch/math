import OAI.Analysis.FiniteFactor.Sampling.LayerCake

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem sampling_measureReal_le_one {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (S : Set α) : |(ρ S).toReal| ≤ 1 := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ (ρ Set.univ).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ S))
    _ = 1 := by simp

/-- Joint superlevel probabilities are measurable in both thresholds. -/
theorem sampling_levelMass_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : ℝ × ℝ => (μ {x | p.1 ≤ f x ∧ p.2 ≤ g x}).toReal) := by
  let K : (ℝ × ℝ) × Ω → ℝ := fun p =>
    if p.1.1 ≤ f p.2 ∧ p.1.2 ≤ g p.2 then 1 else 0
  have hK : Measurable K := measurable_const.ite
    ((measurableSet_le measurable_fst.fst (hf.comp measurable_snd)).inter
      (measurableSet_le measurable_fst.snd (hg.comp measurable_snd))) measurable_const
  have he (p : ℝ × ℝ) : (∫ x, K (p,x) ∂μ) =
      (μ {x | p.1 ≤ f x ∧ p.2 ≤ g x}).toReal := by
    have hs : MeasurableSet {x | p.1 ≤ f x ∧ p.2 ≤ g x} :=
      (measurableSet_le measurable_const hf).inter (measurableSet_le measurable_const hg)
    have hk : (fun x => K (p,x)) =
        {x | p.1 ≤ f x ∧ p.2 ≤ g x}.indicator (fun _ => (1 : ℝ)) := by
      funext x; simp [K,Set.indicator]
    rw [hk,integral_indicator hs]
    simp [measureReal_def]
  have hKm : StronglyMeasurable (Function.uncurry (fun p x => K (p,x))) := hK.stronglyMeasurable
  simpa only [he] using (hKm.integral_prod_right (ν := μ)).measurable

/-- Uniform superlevel discrepancy controls weighted pair integrals. The
threshold square has area C^2; no density for the joint law is needed. -/
theorem sampling_layer_discrepancy {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f g : Ω → ℝ) (f₀ g₀ : Ψ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf₀ : Measurable f₀) (hg₀ : Measurable g₀)
    (C δ : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ C) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ C)
    (hf₀b : ∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ C) (hg₀b : ∀ x, 0 ≤ g₀ x ∧ g₀ x ≤ C)
    (hlevel : ∀ r t : ℝ, 0 < r → r ≤ C → 0 < t → t ≤ C →
      |(μ {x | r ≤ f x ∧ t ≤ g x}).toReal -
        (ν {x | r ≤ f₀ x ∧ t ≤ g₀ x}).toReal| ≤ δ) :
    |(∫ x, f x*g x ∂μ)-(∫ x, f₀ x*g₀ x ∂ν)| ≤ δ*C^2 := by
  let τ := volume.restrict (Set.Ioc 0 C)
  let F : ℝ × ℝ → ℝ := fun p => (μ {x | p.1 ≤ f x ∧ p.2 ≤ g x}).toReal
  let G : ℝ × ℝ → ℝ := fun p => (ν {x | p.1 ≤ f₀ x ∧ p.2 ≤ g₀ x}).toReal
  have hFm : Measurable F := sampling_levelMass_measurable μ f g hf hg
  have hGm : Measurable G := sampling_levelMass_measurable ν f₀ g₀ hf₀ hg₀
  have hFi := sampling_integrable_bounded (τ.prod τ) F hFm 1 (fun p => by dsimp [F]; exact sampling_measureReal_le_one μ _)
  have hGi := sampling_integrable_bounded (τ.prod τ) G hGm 1 (fun p => by dsimp [G]; exact sampling_measureReal_le_one ν _)
  rw [sampling_product_layerCake μ f g hf hg C hC hfb hgb,
    sampling_product_layerCake ν f₀ g₀ hf₀ hg₀ C hC hf₀b hg₀b]
  change |(∫ r, ∫ t, F (r,t) ∂τ ∂τ)-(∫ r, ∫ t, G (r,t) ∂τ ∂τ)| ≤ _
  rw [← integral_prod F hFi,← integral_prod G hGi,← integral_sub hFi hGi]
  have hb : ∀ᵐ p ∂τ.prod τ, ‖F p-G p‖ ≤ δ := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {p : ℝ × ℝ | ‖F p-G p‖ ≤ δ} from
      measurableSet_le (hFm.sub hGm).norm measurable_const)).mpr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    simpa [Real.norm_eq_abs,F,G] using hlevel r t hr.1 hr.2 ht.1 ht.2
  have hi := norm_integral_le_of_norm_le_const hb
  have hm : (τ.prod τ).real Set.univ = C^2 := by
    rw [measureReal_def,← Set.univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
    simp [τ,Real.volume_Ioc,ENNReal.toReal_ofReal hC,pow_two]
  simpa only [Real.norm_eq_abs,hm,mul_comm] using hi

end
end FiniteFactor

end OAI
