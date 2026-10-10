import OAI.Probability.InvariantIsing.Fields.PriorReplicaAverage
import OAI.Probability.InvariantIsing.Arrays.TensorCascadeReplicaAverage
import OAI.Probability.InvariantIsing.Arrays.TensorCountableWard
import OAI.Probability.InvariantIsing.Arrays.TensorCountableDiagonalWard

namespace OAI

/-! The principal Ward bounds hold for each fixed constrained spin prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma priorNamespacedReplicaAverage_reference {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0≤h 0)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ) :
    priorNamespacedReplicaAverage μ ν eig c I degree amp r h D =
      ∫ z : SpecialOrthogonal N × (ℕ → ℝ), referenceReplicaMean ν
        (tensorRestrictionHamiltonian eig c I degree amp
          (fun a => tensorPathProfile I degree n r h a) id z.1 z.2) (D z.1)
        ∂μ.prod gaussianCoordinates := by
  unfold priorNamespacedReplicaAverage
  apply integral_congr_ae
  filter_upwards [priorNamespaced_exp_integrable_ae μ ν eig c I degree amp r h hh h0] with z hz
  exact referenceReplicaMean_gibbsProbability ν _ hz _

theorem priorNamespaced_off_principal_bound {N m n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (r : Fin N → ℕ) (u : Fin N → ℝ)
    (hu : ∀ j, |u j|≤2) (D : ℝ) (hD : 0≤D)
    (hd : ∀ j, (∑ a, (degree j a : ℝ))≤D*((j : ℝ)+1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0≤h 0)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0≤B) (hF : ∀ σ τ, |F σ τ|≤B) :
    |priorNamespacedReplicaAverage μ ν eig c I degree (tensorPerturbationAmplitude N u) r h
        (fun U => tensorOffDirect eig J K Prod.fst F U) -
      2*priorNamespacedReplicaAverage μ ν eig c I degree (tensorPerturbationAmplitude N u) r h
        (fun U => tensorOffFresh eig J K Prod.fst F U)|≤192*B*D*perturbationScale N^2 := by
  rw [priorNamespacedReplicaAverage_reference μ ν eig c I degree _ r h hh h0,
    priorNamespacedReplicaAverage_reference μ ν eig c I degree _ r h hh h0]
  exact tensorCountable_off_principal_bound hN μ ν eig c I degree r u hu D hD hd
    h hh h0 id J K hJK F B hB hF

theorem priorNamespaced_diagonal_principal_bound {N m n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (r : Fin N → ℕ) (u : Fin N → ℝ)
    (hu : ∀ j, |u j|≤2) (D : ℝ) (hD : 0≤D)
    (hd : ∀ j, (∑ a, (degree j a : ℝ))≤D*((j : ℝ)+1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0≤h 0)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    |priorNamespacedReplicaAverage μ ν eig c I degree (tensorPerturbationAmplitude N u) r h
        (tensorDiagonalDirect eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      priorNamespacedReplicaAverage μ ν eig c I degree (tensorPerturbationAmplitude N u) r h
        (tensorDiagonalFresh eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N))|≤
      48*D*perturbationScale N^2 := by
  rw [priorNamespacedReplicaAverage_reference μ ν eig c I degree _ r h hh h0,
    priorNamespacedReplicaAverage_reference μ ν eig c I degree _ r h hh h0]
  exact tensorCountable_diagonal_principal_bound hN μ ν eig c I degree r u hu D hD hd
    h hh h0 id J K hJK

end InvariantIsing

end

end OAI
