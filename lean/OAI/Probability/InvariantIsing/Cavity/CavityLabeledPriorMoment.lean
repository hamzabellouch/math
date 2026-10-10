import OAI.Probability.InvariantIsing.Cavity.CavityLabeledPriorLaw
import OAI.Probability.InvariantIsing.Cavity.CavityLinearGaussianMoment

namespace OAI

/-! Ordinary fourth moments of the actual labeled prior follow from
its Gaussian endpoint law, uniformly in the number of cascade levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gaussian_fourth_moment_bound {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    {M : ℝ} (hSM : ‖S‖ ≤ M) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖^4) (multivariateGaussian 0 S) ∧
    (∫ y : EuclideanSpace ℝ (Fin d), ‖y‖^4 ∂multivariateGaussian 0 S) ≤
      cavityGaussianLinearMomentBound d 4 0 M := by
  have hi : Integrable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖^4)
      (multivariateGaussian 0 S) := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)
        4 (by norm_num)).integrable_norm_pow'
  have he := cavity_gaussian_linear_envelope S hS hSM (le_refl (0 : ℝ)) 4
  refine ⟨hi, (integral_mono hi he.1 fun y => ?_).trans he.2⟩
  have hb := (cavity_linear_envelope_bounds 4 (le_refl (0 : ℝ)) (norm_nonneg y)
    (show |(0 : ℝ)| ≤ 0 * (1 + ‖y‖) by simp)).2.2.2.1
  simpa only [Real.exp_zero, mul_one] using hb

theorem cavity_prior_fourth_moment_of_gaussian_law {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (E : Ω × X → EuclideanSpace ℝ (Fin d)) (hE : Measurable E)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (P ⊗ₘ κ).map E = multivariateGaussian 0 S) {M : ℝ} (hM : ‖S‖ ≤ M) :
    (∀ᵐ ω ∂P, Integrable (fun x => ‖E (ω, x)‖^4) (κ ω)) ∧
    Integrable (fun ω => ∫ x, ‖E (ω, x)‖^4 ∂κ ω) P ∧
    (∫ ω, ∫ x, ‖E (ω, x)‖^4 ∂κ ω ∂P) ≤ cavityGaussianLinearMomentBound d 4 0 M := by
  have hG := cavity_gaussian_fourth_moment_bound S hS hM
  have hi : Integrable (fun p => ‖E p‖^4) (P ⊗ₘ κ) := by
    have ht := hG.1
    rw [← hLaw] at ht
    exact (integrable_map_measure (by fun_prop) hE.aemeasurable).mp ht
  have hp := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi
  refine ⟨hp.1, ?_, ?_⟩
  · simpa only [norm_pow, norm_norm] using hp.2
  · have heq : (∫ ω, ∫ x, ‖E (ω, x)‖^4 ∂κ ω ∂P) =
        ∫ y : EuclideanSpace ℝ (Fin d), ‖y‖^4 ∂multivariateGaussian 0 S := by
      rw [← Measure.integral_compProd hi, ← hLaw, integral_map hE.aemeasurable (by fun_prop)]
    exact heq.le.trans hG.2

theorem cavity_labeled_prior_fourth_moment {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] {M : ℝ}
    (hM : ‖(S₀ + ∑ i : Fin n, S i) + R‖ ≤ M) :
    (∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S,
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω, x)).1‖^4)
        (cavityLabeledPriorKernel n R π ω)) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω) (cavityLabeledDisorderLaw n b S₀ S) ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω ∂cavityLabeledDisorderLaw n b S₀ S) ≤
        cavityGaussianLinearMomentBound d 4 0 M := by
  have hpos : ((S₀ + ∑ i : Fin n, S i) + R).PosSemidef :=
    (hS₀.add (Matrix.posSemidef_sum (Finset.univ : Finset (Fin n)) fun i _ => hS i)).add hR
  exact cavity_prior_fourth_moment_of_gaussian_law
    (Ω := CavityLabeledDisorder d n) (X := CavityLabeledState d k n) (d := d)
    (cavityLabeledDisorderLaw n b S₀ S) (cavityLabeledPriorKernel n R π)
    (fun p => (cavityLabeledEndpoint n p).1) (measurable_cavityLabeledEndpoint (d := d) (k := k) n).fst
    ((S₀ + ∑ i : Fin n, S i) + R)
    hpos
    (cavity_labeled_prior_endpoint_law n b S₀ R S hS₀ hR hS π) hM

end InvariantIsing

end

end OAI
