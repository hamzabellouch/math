import OAI.Probability.InvariantIsing.Fields.SpinPriorPrincipalWard
import OAI.Probability.InvariantIsing.Fields.SpinPriorArrayLaw
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalWardLimits
import OAI.Probability.InvariantIsing.Arrays.TensorArrayDiagonalWard

namespace OAI

/-! The actual enriched diagonal Ward bound is exactly the corresponding
spectral-array residual, retaining the common rotation in both replicas. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal

namespace InvariantIsing

lemma spinPriorArrayLaw_diagonalWard_residual {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (κ : Fin m → ℝ) (a d : Fin m)
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    spectralDiagonalWardResidual (spinPriorArrayLaw μ π eig c I degree amp n b treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d =
      spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
  let ρ := fun j => ((I j).card : ℝ) / N
  let Q := spinPriorArrayLaw μ π eig c I degree amp n b treeDegree h
  have hdir : (∫ x, spectralDiagonalWardDirect ρ κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply spinPriorArrayLaw_test μ π eig c I degree amp n b treeDegree h
      _ (continuous_spectralDiagonalWardDirect ρ κ a d) _
      (fun i : Fin 1 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalDirect_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardDirect, tensorDiagonalBlockDirect, spectralJointEntry_spectral, ρ, Fin.val_zero]
    ring
  have hfresh : (∫ x, spectralDiagonalWardFresh κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply spinPriorArrayLaw_test μ π eig c I degree amp n b treeDegree h
      _ (continuous_spectralDiagonalWardFresh κ a d) _
      (fun i : Fin 2 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalFresh_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardFresh, tensorDiagonalBlockFresh, spectralJointEntry_spectral, Fin.val_zero, Fin.val_one]
    ring
  rw [spectralDiagonalWardResidual_integral Q ρ κ a d, hdir, hfresh]

/-- Exact finite-volume spectral-array diagonal Ward bound for the actual
tensor-enriched law, before taking any overlap limit. -/
theorem spinPriorArrayLaw_diagonalWard_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ j, (degree r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (κ : Fin m → ℝ) (a d : Fin m) (had : Disjoint (I a) (I d))
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    |spectralDiagonalWardResidual
      (spinPriorArrayLaw μ π eig c I degree (tensorPerturbationAmplitude N u) n b treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d| ≤ 48 * D * perturbationScale N ^ 2 := by
  rw [spinPriorArrayLaw_diagonalWard_residual μ π eig c I degree (tensorPerturbationAmplitude N u)
    b treeDegree h κ a d ha hd]
  exact spinPrior_diagonal_principal_bound hN μ π eig c I degree treeDegree u hu D hD hdegree
    b h hh h0 (I a) (I d) had

end InvariantIsing

end

end OAI
