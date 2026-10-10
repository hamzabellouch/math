import OAI.Probability.InvariantIsing.Arrays.TensorReplicaAverageLaw
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalCenters

namespace OAI

/-! Both frozen coordinates control observables in the same actual Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorNamespacedObservableAverage {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p : TensorFlatDisorder N n, ∫ x, D p.1.1 x
    ∂tensorNamespacedReference eig c I degree amplitude n r h p
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates

lemma measurable_tensorNamespacedObservableMean {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x
      ∂tensorNamespacedReference eig c I degree amplitude n r h p) := by
  have hm := measurable_random_tilted_integral
    (measurable_tensorNamespacedReference eig c I degree amplitude n r h)
    (H := fun _ => 0) measurable_const
    (hD.comp (measurable_fst.fst.fst.prodMk measurable_snd))
  change Measurable (fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x
    ∂(tensorNamespacedReference eig c I degree amplitude n r h p).tilted 0) at hm
  simpa only [tilted_zero] using hm

theorem tensorFrozenGaussian_observableAverage {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (t : ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    (∫ p : TensorFrozenData N n j × (ℕ → ℝ), ∫ x, D p.1.1.1 x
      ∂(tensorFrozenReference eig c I degree amplitude n r h j p.1).tilted
        (fun x => t * cylinderField (jointSpectralMonomialCoefficients
          (specialRotation p.1.1.1) I (degree j) n (r j) x) p.2)
      ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) =
      tensorNamespacedObservableAverage μ eig c I degree (Function.update amplitude j t) n b r h D := by
  let F := fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x
    ∂tensorNamespacedReference eig c I degree (Function.update amplitude j t) n r h p
  have hF : Measurable F := measurable_tensorNamespacedObservableMean eig c I degree
    (Function.update amplitude j t) n r h D hD
  calc
    _ = ∫ p : TensorFrozenData N n j × (ℕ → ℝ),
        F (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2))
        ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [tensorFrozenGaussian_reference_fold_ae μ eig c I degree amplitude n b r h hh h0 j t]
        with p hp
      rw [hp]
    _ = _ := (tensorFrozenInsertion_measurePreserving μ n b j).hasLaw.integral_comp hF.aestronglyMeasurable

theorem tensorFrozenDiagonal_observableAverage {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ) :
    (∫ p : TensorFlatDisorder N n, ∫ x, D p.1.1 x
      ∂(tensorNamespacedReference (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
        c I degree amplitude n r h p).tilted
        (fun x : Spin N × LabeledLeaf n => N * perturbationScale N * w *
          projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) =
      tensorNamespacedObservableAverage μ
        (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n b r h D := by
  apply integral_congr_ae
  filter_upwards [tensorFrozenDiagonal_reference_fold_ae hN μ eig c I degree amplitude n b r h hh h0 v t a w]
    with p hp
  rw [hp]

lemma tensorNamespacedObservableAverage_integrable {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) {B : ℝ} (hB : ∀ U x, |D U x| ≤ B) :
    Integrable (fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x
      ∂tensorNamespacedReference eig c I degree amplitude n r h p)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  apply Integrable.of_bound
    (measurable_tensorNamespacedObservableMean eig c I degree amplitude n r h D hD).aestronglyMeasurable B
  exact ae_of_all _ fun p => by
    simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := tensorNamespacedReference eig c I degree amplitude n r h p)
        (f := fun x => D p.1.1 x) (C := B) (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs] using hB p.1.1 x)

end InvariantIsing

end

end OAI
