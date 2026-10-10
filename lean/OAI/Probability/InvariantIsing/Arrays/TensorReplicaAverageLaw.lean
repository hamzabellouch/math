import OAI.Probability.InvariantIsing.Arrays.TensorFrozenGibbs
import OAI.Probability.InvariantIsing.Spectral.SpectralGG

namespace OAI

/-! Finite replica averages under the tensor Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma referenceReplicaMean_zero {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {q : ℕ} (D : (Fin q → X) → ℝ) :
    referenceReplicaMean ν (fun _ => 0) D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin q => ν) := by
  rw [referenceReplicaMean_eq_tilted ν (fun _ => 0) (by simp) D]
  simp only [show (fun _ : X => (0 : ℝ)) = 0 from rfl, tilted_zero]

def tensorNamespacedReplicaAverage {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p : TensorFlatDisorder N n,
    referenceReplicaMean (tensorNamespacedReference eig c I degree amplitude n r h p)
      (fun _ => 0) (D p.1.1)
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates

lemma measurable_tensorNamespacedReplicaMean {N m k q : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun p : TensorFlatDisorder N n =>
      referenceReplicaMean (tensorNamespacedReference eig c I degree amplitude n r h p)
        (fun _ => 0) (D p.1.1)) := by
  exact measurable_random_referenceReplicaMean
    (measurable_tensorNamespacedReference eig c I degree amplitude n r h) measurable_const
    (hD.comp (measurable_fst.fst.fst.prodMk measurable_snd))

/-- Gaussian insertion and actual full-model sampling give exactly the
same bounded finite-replica averages, retaining the common Haar rotation. -/
theorem tensorFrozenGaussian_replicaAverage {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (t : ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    let U := fun ω : TensorFrozenData N n j => ω.1.1
    randomCoefficientAverage (tensorFrozenLaw μ n b j)
      (tensorFrozenReference eig c I degree amplitude n r h j)
      (spectralPerturbationCoefficients U I (degree j) n (r j)) t (fun ω => D (U ω)) =
      tensorNamespacedReplicaAverage μ eig c I degree (Function.update amplitude j t) n b r h D := by
  intro U
  let ν := tensorFrozenReference eig c I degree amplitude n r h j
  let A := spectralPerturbationCoefficients U I (degree j) n (r j)
  have hAm := measurable_spectralPerturbationFields U measurable_fst.fst I (degree j) n (r j)
  have hA (ω : TensorFrozenData N n j) (x : Spin N × LabeledLeaf n) :
      (A ω x).sum (fun _ c => c ^ 2) ≤ 1 :=
    jointSpectralMonomialCoefficients_variance_le_one (specialRotation (U ω)) I (degree j) n (r j) x
  have he := randomCoefficient_all_exp_ae (P := tensorFrozenLaw μ n b j)
    (measurable_tensorFrozenReference eig c I degree amplitude n r h j) A hAm hA
  have hf := tensorFrozenGaussian_reference_fold_ae μ eig c I degree amplitude n b r h hh h0 j t
  let F := fun p : TensorFlatDisorder N n =>
    referenceReplicaMean (tensorNamespacedReference eig c I degree (Function.update amplitude j t) n r h p)
      (fun _ => 0) (D p.1.1)
  have hF : Measurable F := measurable_tensorNamespacedReplicaMean eig c I degree
    (Function.update amplitude j t) n r h D hD
  unfold randomCoefficientAverage
  calc
    _ = ∫ p : TensorFrozenData N n j × (ℕ → ℝ),
        F (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2))
        ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [he, hf] with p hp hpf
      rw [referenceReplicaMean_eq_tilted _ _ (hp t)]
      change (∫ σ, D (U p.1) σ ∂Measure.pi
        (fun _ : Fin q => (ν p.1).tilted (fun x => t * cylinderField (A p.1 x) p.2))) = _
      have hpf' : (ν p.1).tilted (fun x => t * cylinderField (A p.1 x) p.2) =
          tensorNamespacedReference eig c I degree (Function.update amplitude j t) n r h
            (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2)) := hpf
      rw [hpf']
      exact (referenceReplicaMean_zero _ _).symm
    _ = _ := (tensorFrozenInsertion_measurePreserving μ n b j).hasLaw.integral_comp
      hF.aestronglyMeasurable

end InvariantIsing

end

end OAI
