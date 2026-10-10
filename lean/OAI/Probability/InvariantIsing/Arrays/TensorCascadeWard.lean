import OAI.Probability.InvariantIsing.Arrays.TensorCountableWard
import OAI.Probability.InvariantIsing.Arrays.TensorCascadeReplicaAverage
import OAI.Probability.InvariantIsing.Arrays.CountableWardMixture

namespace OAI

/-! The countable principal Ward bound for the actual enriched Gibbs law,
including the random cascade reference weights. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

 theorem tensorNamespaced_off_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    let amp := tensorPerturbationAmplitude N u
    |tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun U => tensorOffDirect eig J K (fun s : Spin N × LabeledLeaf n => s.1) F U) -
      2 * tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun U => tensorOffFresh eig J K (fun s : Spin N × LabeledLeaf n => s.1) F U)| ≤
      192 * B * D * perturbationScale N ^ 2 := by
  intro amp
  let sp := fun s : Spin N × LabeledLeaf n => s.1
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun a => tensorPathProfile I degree n treeDegree h a
  let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
    tensorRestrictionHamiltonian eig c I degree amp v id z.1.1 z.1.2 z.2
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → Spin N × LabeledLeaf n) =>
    tensorOffDirect eig J K sp F z.1.1 z.2
  let D₃ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 3 → Spin N × LabeledLeaf n) =>
    tensorOffFresh eig J K sp F z.1.1 z.2
  have hm₂ : Measurable (Function.uncurry (fun U => tensorOffDirect eig J K sp F U)) :=
    measurable_tensorOffDirect eig J K sp F
  have hm₃ : Measurable (Function.uncurry (fun U => tensorOffFresh eig J K sp F U)) :=
    measurable_tensorOffFresh eig J K sp F
  rw [tensorNamespacedReplicaAverage_cascade_mixture μ eig c I degree amp n b treeDegree h hh h0
    _ hm₂ (tensorOffDirectCap_nonneg eig J K hB)
      (fun U σ => tensorOffDirect_abs_le eig J K sp F hB hF U σ),
    tensorNamespacedReplicaAverage_cascade_mixture μ eig c I degree amp n b treeDegree h hh h0
    _ hm₃ (tensorOffFreshCap_nonneg eig J K hB)
      (fun U σ => tensorOffFresh_abs_le eig J K sp F hB hF U σ)]
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v id s)
  have hD₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorOffDirect_at eig J K sp F σ).comp measurable_fst)
  have hD₃ : Measurable D₃ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorOffFresh_at eig J K sp F σ).comp measurable_fst)
  apply expectedReplicaWard_mixture_abs_le (labeledCascadeLaw n b : Measure (LabeledTree n))
    (μ.prod gaussianCoordinates)
    (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)))
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))) H hH
    D₂ hD₂ D₃ hD₃ (tensorOffDirectCap_nonneg eig J K hB) (tensorOffFreshCap_nonneg eig J K hB)
    (fun z => tensorOffDirect_abs_le eig J K sp F hB hF z.1.1 z.2)
    (fun z => tensorOffFresh_abs_le eig J K sp F hB hF z.1.1 z.2)
  intro T
  exact tensorCountable_off_principal_bound hN μ
    (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
    eig c I degree treeDegree u hu D hD hdegree h hh h0 id J K hJK F B hB hF

end InvariantIsing

end

end OAI
