import Mathlib
import OAI.Probability.Perceptron.Variational.AtomicPairVisitLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma indexedPairState_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (d : Fin (n+1))
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    (∫ p, (∫ y, f y.1*f y.2 ∂indexedPairStateKernel step hs n F hF x d p)
      ∂((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) =
      (twoVisitMass n z d).toReal *
        pathCorrelation n (fun i => tiltedStateStep ν step (z i) (F i)) f d x := by
  let μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
    (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
  let κ := indexedPairStateKernel step hs n F hF x d
  have ht : Measurable (fun y : X×X => f y.1*f y.2) :=
    (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hB : ∀ y : X×X, |f y.1*f y.2| ≤ C^2 := fun y => by
    rw [abs_mul,pow_two]; exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hC
  have hi := path_bounded_integrable (κ ∘ₘ μ) _ ht (C^2) hB
  have he : (∫ y, f y.1*f y.2 ∂(κ ∘ₘ μ)) = ∫ p, ∫ y, f y.1*f y.2 ∂κ p ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hi ⊢
    exact Kernel.integral_comp hi
  rw [← he]
  change (∫ y, f y.1*f y.2 ∂(indexedPairStateKernel step hs n F hF x d ∘ₘ _)) = _
  rw [indexedPairStateLaw_eq ν step hs n z hz hz0 hz1 F hF hI hM x d,
    integral_smul_measure,smul_eq_mul]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
