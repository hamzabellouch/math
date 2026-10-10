import OAI.Probability.InvariantIsing.Fields.PriorPrincipalWard
import OAI.Probability.InvariantIsing.Fields.PriorArrayLaw
import OAI.Probability.InvariantIsing.Arrays.TensorArrayDiagonalWard

namespace OAI

/-! Finite diagonal Ward residual for the actual constrained-prior array. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal
namespace InvariantIsing

lemma priorNamespacedArrayLaw_diagonalWard_residual {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (κ : Fin m → ℝ) (a d : Fin m)
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    spectralDiagonalWardResidual (priorNamespacedArrayLaw μ ν eig c I degree amp treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d =
      priorNamespacedReplicaAverage μ ν eig c I degree amp treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      priorNamespacedReplicaAverage μ ν eig c I degree amp treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
  let ρ := fun j => ((I j).card : ℝ) / N
  let Q := priorNamespacedArrayLaw μ ν eig c I degree amp treeDegree h
  have hdir : (∫ x, spectralDiagonalWardDirect ρ κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      priorNamespacedReplicaAverage μ ν eig c I degree amp treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply priorNamespacedArrayLaw_test μ ν eig c I degree amp treeDegree h
      _ (continuous_spectralDiagonalWardDirect ρ κ a d) _
      (fun i : Fin 1 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalDirect_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardDirect, tensorDiagonalBlockDirect, spectralJointEntry_spectral, ρ, Fin.val_zero]
    ring
  have hfresh : (∫ x, spectralDiagonalWardFresh κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      priorNamespacedReplicaAverage μ ν eig c I degree amp treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply priorNamespacedArrayLaw_test μ ν eig c I degree amp treeDegree h
      _ (continuous_spectralDiagonalWardFresh κ a d) _
      (fun i : Fin 2 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalFresh_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardFresh, tensorDiagonalBlockFresh, spectralJointEntry_spectral, Fin.val_zero, Fin.val_one]
    ring
  rw [spectralDiagonalWardResidual_integral Q ρ κ a d, hdir, hfresh]

/-- Exact finite-volume spectral-array diagonal Ward bound for the actual
tensor-enriched law, before taking any overlap limit. -/
theorem priorNamespacedArrayLaw_diagonalWard_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ j, (degree r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (κ : Fin m → ℝ) (a d : Fin m) (had : Disjoint (I a) (I d))
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    |spectralDiagonalWardResidual
      (priorNamespacedArrayLaw μ ν eig c I degree (tensorPerturbationAmplitude N u) treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d| ≤ 48 * D * perturbationScale N ^ 2 := by
  rw [priorNamespacedArrayLaw_diagonalWard_residual μ ν eig c I degree (tensorPerturbationAmplitude N u)
    treeDegree h κ a d ha hd]
  exact priorNamespaced_diagonal_principal_bound hN μ ν eig c I degree treeDegree u hu D hD hdegree
    h hh h0 (I a) (I d) had


end InvariantIsing

end

end OAI
