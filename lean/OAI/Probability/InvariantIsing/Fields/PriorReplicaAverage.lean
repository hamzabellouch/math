import OAI.Probability.InvariantIsing.Fields.PriorFrozenGibbs
import OAI.Probability.InvariantIsing.Arrays.TensorReplicaAverageLaw

namespace OAI

/-! Observable and replica averages for the actual fixed-prior Gibbs measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def priorNamespacedObservableAverage {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ) : ℝ :=
  ∫ p : SpecialOrthogonal N × (ℕ → ℝ), ∫ x, D p.1 x
    ∂priorNamespacedReference ν eig c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p
    ∂μ.prod gaussianCoordinates

lemma measurable_priorNamespacedObservableMean {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => ∫ x, D p.1 x
      ∂priorNamespacedReference ν eig c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p) := by
  have hm := measurable_random_tilted_integral
    (measurable_priorNamespacedReference ν eig c I degree amplitude
      (fun i => tensorPathProfile I degree n r h i))
    (H := fun _ => 0) measurable_const (hD.comp (measurable_fst.fst.prodMk measurable_snd))
  change Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => ∫ x, D p.1 x
    ∂(priorNamespacedReference ν eig c I degree amplitude
      (fun i => tensorPathProfile I degree n r h i) p).tilted 0) at hm
  simpa only [tilted_zero] using hm

lemma priorNamespacedObservableAverage_integrable {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ)
    (hD : Measurable (Function.uncurry D)) {B : ℝ} (hB : ∀ U x, |D U x|≤B) :
    Integrable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => ∫ x, D p.1 x
      ∂priorNamespacedReference ν eig c I degree amplitude
        (fun i => tensorPathProfile I degree n r h i) p) (μ.prod gaussianCoordinates) := by
  apply Integrable.of_bound
    (measurable_priorNamespacedObservableMean ν eig c I degree amplitude r h D hD).aestronglyMeasurable B
  exact ae_of_all _ fun p => by
    simpa only [probReal_univ,mul_one,Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := priorNamespacedReference ν eig c I degree amplitude
          (fun i => tensorPathProfile I degree n r h i) p)
        (f := fun x => D p.1 x) (C := B) (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs] using hB p.1 x)

theorem priorFrozenGaussian_observableAverage {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin k) (t : ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    (∫ p : PriorFrozenData N j × (ℕ → ℝ), ∫ x, D p.1.1 x
      ∂(priorFrozenReference ν eig c I degree amplitude r h j p.1).tilted
        (fun x => t*cylinderField (jointSpectralMonomialCoefficients
          (specialRotation p.1.1) I (degree j) n (r j) x) p.2)
      ∂(priorFrozenLaw μ j).prod gaussianCoordinates) =
      priorNamespacedObservableAverage μ ν eig c I degree (Function.update amplitude j t) r h D := by
  let F := fun p : SpecialOrthogonal N × (ℕ → ℝ) => ∫ x, D p.1 x
    ∂priorNamespacedReference ν eig c I degree (Function.update amplitude j t)
      (fun i => tensorPathProfile I degree n r h i) p
  have hF := measurable_priorNamespacedObservableMean ν eig c I degree (Function.update amplitude j t) r h D hD
  calc
    _ = ∫ p, F (priorFrozenInsertion j p) ∂(priorFrozenLaw μ j).prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [priorFrozenGaussian_reference_fold_ae μ ν eig c I degree amplitude r h hh h0 j t]
        with p hp
      rw [hp]
      rfl
    _ = _ := (priorFrozenInsertion_preserving μ j).hasLaw.integral_comp hF.aestronglyMeasurable

theorem priorFrozenDiagonal_observableAverage {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ) :
    (∫ p : SpecialOrthogonal N × (ℕ → ℝ), ∫ x, D p.1 x
      ∂(priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p).tilted
        (fun x => N*perturbationScale N*w*projectedOverlap (specialRotation p.1) (I a) x.1 x.1)
      ∂μ.prod gaussianCoordinates) =
      priorNamespacedObservableAverage μ ν
        (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude r h D := by
  apply integral_congr_ae
  filter_upwards [priorFrozenDiagonal_reference_fold_ae hN μ ν eig c I degree amplitude r h hh h0 v t a w]
    with p hp
  rw [hp]

def priorNamespacedReplicaAverage {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p : SpecialOrthogonal N × (ℕ → ℝ),
    referenceReplicaMean (priorNamespacedReference ν eig c I degree amplitude
      (fun i => tensorPathProfile I degree n r h i) p) (fun _ => 0) (D p.1)
    ∂μ.prod gaussianCoordinates

lemma measurable_priorNamespacedReplicaMean {N m k n q : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      referenceReplicaMean (priorNamespacedReference ν eig c I degree amplitude
        (fun i => tensorPathProfile I degree n r h i) p) (fun _ => 0) (D p.1)) :=
  measurable_random_referenceReplicaMean (measurable_priorNamespacedReference ν eig c I degree amplitude _)
    measurable_const (hD.comp (measurable_fst.fst.prodMk measurable_snd))

theorem priorFrozenGaussian_replicaAverage {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin k) (t : ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    let U := fun ω : PriorFrozenData N j => ω.1
    randomCoefficientAverage (priorFrozenLaw μ j) (priorFrozenReference ν₀ eig c I degree amplitude r h j)
      (spectralPerturbationCoefficients U I (degree j) n (r j)) t (fun ω => D (U ω)) =
      priorNamespacedReplicaAverage μ ν₀ eig c I degree (Function.update amplitude j t) r h D := by
  intro U
  let ν := priorFrozenReference ν₀ eig c I degree amplitude r h j
  let A := spectralPerturbationCoefficients U I (degree j) n (r j)
  have he := randomCoefficient_all_exp_ae (P := priorFrozenLaw μ j)
    (measurable_priorFrozenReference ν₀ eig c I degree amplitude r h j) A
    (measurable_spectralPerturbationFields U measurable_fst I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one
      (specialRotation (U ω)) I (degree j) n (r j) x)
  let F := fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
    referenceReplicaMean (priorNamespacedReference ν₀ eig c I degree (Function.update amplitude j t)
      (fun i => tensorPathProfile I degree n r h i) p) (fun _ => 0) (D p.1)
  have hF := measurable_priorNamespacedReplicaMean ν₀ eig c I degree (Function.update amplitude j t) r h D hD
  unfold randomCoefficientAverage
  calc
    _ = ∫ p, F (priorFrozenInsertion j p) ∂(priorFrozenLaw μ j).prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [he,priorFrozenGaussian_reference_fold_ae μ ν₀ eig c I degree amplitude r h hh h0 j t]
        with p hp hf
      rw [referenceReplicaMean_eq_tilted _ _ (hp t)]
      change (∫ σ, D (U p.1) σ ∂Measure.pi (fun _ : Fin q =>
        (ν p.1).tilted (fun x => t*cylinderField (A p.1 x) p.2))) = _
      change (ν p.1).tilted (fun x => t*cylinderField (A p.1 x) p.2) = _ at hf
      rw [hf]
      exact (referenceReplicaMean_zero _ _).symm
    _ = _ := (priorFrozenInsertion_preserving μ j).hasLaw.integral_comp hF.aestronglyMeasurable

end InvariantIsing

end

end OAI
