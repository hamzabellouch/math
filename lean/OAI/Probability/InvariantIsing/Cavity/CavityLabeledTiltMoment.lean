import OAI.Probability.InvariantIsing.Cavity.CavityLabeledPriorTransport
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteOriginalMoment

namespace OAI

/-! Transport of full tilted radial moments to the fixed-state labeled
cavity model used in the normalized replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityLabeledRootMap_field {d k : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n)
    (x : CavityLabeledState d k n) :
    cavityRootedField n (cavityLabeledRootMap n ω x).1 = (cavityLabeledEndpoint n (ω,x)).1 := by
  simp only [cavityLabeledRootMap, Function.comp_apply, cavityAttachSpinRoot,
    cavityLabeledSpinMap, cavityRootedField, cavity_labeled_leaf_sum,
    cavityLabeledEndpoint, cavityLabeledField]

theorem cavity_labeled_tilted_radial_moment {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ℓ : ℕ) {M : ℝ}
    (hI : ∀ᵐ ω ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      Integrable (fun x => Real.exp (cavityLogFactor K L C (cavityRootedField n x.1) x.2))
        ((cavityRootedPriorKernel n R ω).prod π))
    (hMom : (∀ᵐ ω ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      Integrable (fun x => ‖cavityRootedField n x.1‖^ℓ)
        (((cavityRootedPriorKernel n R ω).prod π).tilted
          (fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2))) ∧
      Integrable (fun ω => ∫ x, ‖cavityRootedField n x.1‖^ℓ
        ∂((cavityRootedPriorKernel n R ω).prod π).tilted
          (fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2))
        ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)) ∧
      (∫ ω, ∫ x, ‖cavityRootedField n x.1‖^ℓ
        ∂((cavityRootedPriorKernel n R ω).prod π).tilted
          (fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)) ≤ M) :
    (∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S,
      Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n R π ω) ∧
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
        ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))
      (cavityLabeledDisorderLaw n b S₀ S) ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))
      ∂cavityLabeledDisorderLaw n b S₀ S) ≤ M := by
  let V : CavitySpinState d k n → ℝ := fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2
  let J := fun ω => ∫ x, ‖cavityRootedField n x.1‖^ℓ
    ∂((cavityRootedPriorKernel n R ω).prod π).tilted V
  let f := cavityLabeledNoiseDisorderMap (d := d) n
  let P := cavityLabeledDisorderLaw n b S₀ S
  let A := fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
    ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))
  have hmap := cavity_labeled_noise_disorder_law n b S₀ S
  have hgood := cavity_labeled_disorder_good n b S₀ S hb
  have hpulled := hmap.quasiMeasurePreserving.ae (hI.and hMom.1)
  have hpoint : ∀ᵐ ω ∂P,
      Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n R π ω) ∧
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
        ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))) ∧
      A ω = J (f ω) := by
    filter_upwards [hpulled, hgood] with ω hω hg
    have heI := cavity_labeled_model_exp_integrable n K R L C π ω hg.1 hg.2 hω.1
    have hm := cavity_labeled_model_tilted_law n K R L C π ω hg.1 hg.2 hω.1
    rw [cavityRootedFullGibbs_eq_tilted n K R L C π _ hω.1] at hm
    have hi : Integrable (fun x : CavitySpinState d k n => ‖cavityRootedField n x.1‖^ℓ)
        (((cavityLabeledPriorKernel n R π ω).tilted
          (fun x => cavityLabeledPotential n K L C (ω,x))).map (cavityLabeledRootMap n ω)) := by
      rw [hm]
      exact hω.2
    have hInt := (integrable_map_measure hi.aestronglyMeasurable
      (measurable_cavityLabeledRootMap n ω).aemeasurable).mp hi
    have hEq := integral_map (measurable_cavityLabeledRootMap n ω).aemeasurable
      (show AEStronglyMeasurable (fun x : CavitySpinState d k n => ‖cavityRootedField n x.1‖^ℓ)
        (((cavityLabeledPriorKernel n R π ω).tilted
          (fun x => cavityLabeledPotential n K L C (ω,x))).map (cavityLabeledRootMap n ω)) from
        hi.aestronglyMeasurable)
    simp only [Function.comp_def, cavityLabeledRootMap_field] at hInt hEq
    refine ⟨heI, hInt, ?_⟩
    change _ = A ω at hEq
    rw [hm] at hEq
    exact hEq.symm
  have hj := hmap.integrable_comp_of_integrable hMom.2.1
  have ha : A =ᵐ[P] J ∘ f := hpoint.mono (fun _ h => h.2.2)
  refine ⟨hpoint.mono (fun _ h => ⟨h.1,h.2.1⟩), hj.congr ha.symm, ?_⟩
  rw [integral_congr_ae ha]
  exact (hmap.hasLaw.integral_comp hMom.2.1.aestronglyMeasurable).le.trans hMom.2.2

end InvariantIsing

end

end OAI
