import OAI.Probability.InvariantIsing.Cavity.CavityLabeledDisorderLaw

namespace OAI

/-! The fixed-state finite model prior and potential are exactly the
labeled realization of the original common-root cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

def cavityLabeledRootMap {d k : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n) :
    CavityLabeledState d k n → CavitySpinState d k n :=
  cavityAttachSpinRoot n ω.2.1 ∘ cavityLabeledSpinMap n ω.1 ω.2.2

lemma measurable_cavityLabeledRootMap {d k : ℕ} (n : ℕ)
    (ω : CavityLabeledDisorder d n) :
    Measurable (cavityLabeledRootMap (k := k) n ω) :=
  (measurable_cavityAttachSpinRoot n ω.2.1).comp
    (measurable_cavityLabeledSpinMap n ω.1 ω.2.2)

lemma cavityLabeledRootMap_potential {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (ω : CavityLabeledDisorder d n)
    (x : CavityLabeledState d k n) :
    cavityLogFactor K L C (cavityRootedField n (cavityLabeledRootMap n ω x).1)
      (cavityLabeledRootMap n ω x).2 = cavityLabeledPotential n K L C (ω,x) := by
  simp only [cavityLabeledRootMap, Function.comp_apply, cavityAttachSpinRoot,
    cavityLabeledSpinMap, cavityRootedField, cavity_labeled_leaf_sum,
    cavityLabeledPotential, cavityLabeledEndpoint, cavityLabeledField]

lemma cavity_labeled_model_prior_law {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n)
    (hg : GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2)
    (ht : 0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞) :
    MeasurePreserving (cavityLabeledRootMap n ω) (cavityLabeledPriorKernel n R π ω)
      ((cavityRootedPriorKernel n R (cavityLabeledNoiseDisorderMap n ω)).prod π) := by
  rw [cavityLabeledPriorKernel_apply]
  exact (cavity_attach_spin_root_prior_law n R ω.2.1 _ π).comp
    (cavity_labeled_spin_prior_law n ω.1 ω.2.2 hg ht R π)

lemma cavity_labeled_model_exp_integrable {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n)
    (hg : GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2)
    (ht : 0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞)
    (hI : Integrable (fun z => Real.exp
      (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n R (cavityLabeledNoiseDisorderMap n ω)).prod π)) :
    Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
      (cavityLabeledPriorKernel n R π ω) := by
  have hi := (cavity_labeled_model_prior_law n R π ω hg ht).integrable_comp_of_integrable hI
  simpa only [Function.comp_def, cavityLabeledRootMap_potential] using hi

lemma cavity_labeled_model_tilted_law {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n)
    (hg : GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2)
    (ht : 0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞)
    (hI : Integrable (fun z => Real.exp
      (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n R (cavityLabeledNoiseDisorderMap n ω)).prod π)) :
    ((cavityLabeledPriorKernel n R π ω).tilted
      (fun x => cavityLabeledPotential n K L C (ω,x))).map (cavityLabeledRootMap n ω) =
      cavityRootedFullGibbs n K R L C π (cavityLabeledNoiseDisorderMap n ω) := by
  have hp := cavity_labeled_model_prior_law n R π ω hg ht
  rw [cavityRootedFullGibbs_eq_tilted n K R L C π _ hI]
  let V : CavitySpinState d k n → ℝ := fun z =>
    cavityLogFactor K L C (cavityRootedField n z.1) z.2
  have hV : Measurable V := measurable_cavityRootedLogFactor n K L C
  have he : (fun x => cavityLabeledPotential n K L C (ω,x)) = V ∘ cavityLabeledRootMap n ω :=
    funext fun x => (cavityLabeledRootMap_potential n K L C ω x).symm
  rw [he, cavity_tilt_map _ _ hp.measurable V hV, hp.map_eq]

end InvariantIsing

end

end OAI
