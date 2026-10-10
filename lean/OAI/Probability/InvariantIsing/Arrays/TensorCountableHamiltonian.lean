import OAI.Probability.InvariantIsing.Arrays.TensorWardMeasurability
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozenCGF

namespace OAI

/-! Exponential integrability of the actual tensor Hamiltonian for every
countable probability prior, before specializing to random cascade weights. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma tensorCountableHamiltonian_exp_integrable_ae {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : X → Spin N × LabeledLeaf n) :
    ∀ᵐ z ∂μ.prod gaussianCoordinates, Integrable
      (fun s => Real.exp (tensorRestrictionHamiltonian eig c I degree amplitude
        (fun a => tensorPathProfile I degree n treeDegree h a) x z.1 z.2 s)) ν := by
  let A := fun (U : SpecialOrthogonal N) (s : X) =>
    tensorNamespacedCoefficients (specialRotation U) I degree amplitude n
      (fun a => tensorPathProfile I degree n treeDegree h a) (x s)
  have hA : Measurable (fun p : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      cylinderField (A p.1.1 p.2) p.1.2) :=
    measurable_from_prod_countable_left (fun s =>
      measurable_tensorNamespacedFields_joint I degree amplitude n
        (fun a => tensorPathProfile I degree n treeDegree h a) (x s))
  have hcap (U : SpecialOrthogonal N) (s : X) :
      (A U s).sum (fun _ c => c ^ 2) ≤ h n * N + ∑ j, amplitude j ^ 2 :=
    tensorNamespacedPath_variance_le (specialRotation U) I degree amplitude n treeDegree h hh h0 (x s)
  have he := randomCoefficient_all_exp_ae (P := μ) (ν := fun _ : SpecialOrthogonal N => ν)
    measurable_const A hA hcap
  filter_upwards [he] with z hz
  have hi : Integrable (fun s => Real.exp (cylinderField (A z.1 s) z.2)) ν := by
    simpa only [one_mul] using hz 1
  let E : Spin N → ℝ := orbitHamiltonian eig c (specialToOrthogonal z.1)
  have hb (s : X) : E (x s).1 ≤ ∑ σ : Spin N, |E σ| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun σ _ => abs_nonneg (E σ)) (Finset.mem_univ _))
  exact integrable_exp_bounded_add hi (measurable_of_countable (fun s => E (x s).1)) hb

end InvariantIsing

end

end OAI
