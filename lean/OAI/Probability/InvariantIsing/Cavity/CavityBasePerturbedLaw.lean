import OAI.Probability.InvariantIsing.Cavity.CavityHaarSides
import OAI.Probability.InvariantIsing.Cavity.CavityBaseAmplitude

namespace OAI

/-! The physical base array uses the very same finite perturbation
minimizers as the tensor GG construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_base_perturbed_array_law {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (b : ℕ → ℝ) :
    cavityRotationArrayLaw μ (labeledCascadeLaw depth b : Measure (LabeledTree depth))
      (diagonalPerturbedEigenvalues eig I v t) I (cavityBaseAmplitude u) =
    tensorPerturbedArrayLaw (cavityOrientedBaseLaw hN μ) eig (fun _ => 0) I u v t depth b (fun _ => 0) := by
  unfold tensorPerturbedArrayLaw
  simpa only [cavityBaseAmplitude_restrict] using
    cavity_orientation_array_law hN μ (diagonalPerturbedEigenvalues eig I v t) I (cavityBaseAmplitude u) b

theorem cavity_rotation_minimizers_spectralGG
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega : 0 < N k) (μ k))
        (eig k) (fun _ => 0) (I k) (t k) depth b (fun _ => 0) (u k) (v k) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega : 0 < N k) (μ k))
        (eig k) (fun _ => 0) (I k) (t k) depth b (fun _ => 0) u' v')
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => cavityRotationArrayLaw (μ k)
      (labeledCascadeLaw depth b : Measure (LabeledTree depth))
      (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (I k) (cavityBaseAmplitude (u k)))
      atTop (𝓝 Q)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) := by
  have hpos k : 0 < N k := by have := hN k; omega
  have hEq k := cavity_base_perturbed_array_law (depth := depth)
    (hpos k) (μ k) (eig k) (I k) (u k) (v k) (t k) b
  simp_rw [hEq] at hL
  exact tensorPerturbation_minimizers_spectralGG hhaar hgauss N hN hNlim m depth b hb
    (fun k => cavityOrientedBaseLaw (hpos k) (μ k))
    (fun k => cavityOrientedBaseLaw_leftInvariant (hpos k) (μ k))
    eig (fun _ _ => 0) K hK heig I u hu v hv t ht
    (fun _ _ => 0) (fun _ => monotone_const) (fun _ => le_rfl)
    0 (fun _ => le_rfl) hmin Q hL

end InvariantIsing

end

end OAI
