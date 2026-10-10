import OAI.Probability.InvariantIsing.Fields.SpinPriorReplicaMixture
import OAI.Probability.InvariantIsing.Arrays.TensorCascadeWard
import OAI.Probability.InvariantIsing.Arrays.TensorCascadeDiagonalWard

namespace OAI

/-! Principal Ward bounds for the actual quenched constrained cascade. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

 theorem spinPrior_off_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    let amp := tensorPerturbationAmplitude N u
    |spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
        (fun U => tensorOffDirect eig J K (fun s : Spin N × LabeledLeaf n => s.1) F U) -
      2 * spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
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
  rw [spinPriorReplicaAverage_cascade_mixture μ π eig c I degree amp n b treeDegree h hh h0
    _ hm₂ (tensorOffDirectCap_nonneg eig J K hB)
      (fun U σ => tensorOffDirect_abs_le eig J K sp F hB hF U σ),
    spinPriorReplicaAverage_cascade_mixture μ π eig c I degree amp n b treeDegree h hh h0
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
    (labeledSpinReference n π)
    (measurable_labeledSpinReference_general n π) H hH
    D₂ hD₂ D₃ hD₃ (tensorOffDirectCap_nonneg eig J K hB) (tensorOffFreshCap_nonneg eig J K hB)
    (fun z => tensorOffDirect_abs_le eig J K sp F hB hF z.1.1 z.2)
    (fun z => tensorOffFresh_abs_le eig J K sp F hB hF z.1.1 z.2)
  intro T
  exact tensorCountable_off_principal_bound hN μ
    (labeledSpinReference n π T)
    eig c I degree treeDegree u hu D hD hdegree h hh h0 id J K hJK F B hB hF

theorem spinPrior_diagonal_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    |spinPriorReplicaAverage μ π eig c I degree (tensorPerturbationAmplitude N u)
        n b treeDegree h (tensorDiagonalDirect eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      spinPriorReplicaAverage μ π eig c I degree (tensorPerturbationAmplitude N u)
        n b treeDegree h (tensorDiagonalFresh eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N))| ≤
      48 * D * perturbationScale N ^ 2 := by
  let amp := tensorPerturbationAmplitude N u
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun a => tensorPathProfile I degree n treeDegree h a
  let P := μ.prod gaussianCoordinates
  let ν := labeledSpinReference n π
  let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
    tensorRestrictionHamiltonian eig c I degree amp v id z.1.1 z.1.2 z.2
  let D₁ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 1 → Spin N × LabeledLeaf n) =>
    tensorDiagonalDirect eig J K Prod.fst z.1.1 z.2
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → Spin N × LabeledLeaf n) =>
    tensorDiagonalFresh eig J K Prod.fst z.1.1 z.2
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v id s)
  have hm₁ : Measurable D₁ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalDirect_at eig J K Prod.fst σ).comp measurable_fst)
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalFresh_at eig J K Prod.fst σ).comp measurable_fst)
  have hward (T : LabeledTree n) : |expectedDiagonalWard P (ν T) H D₁ D₂| ≤
      48 * D * perturbationScale N ^ 2 :=
    tensorCountable_diagonal_principal_bound hN μ (ν T) eig c I degree treeDegree u hu D hD
      hdegree h hh h0 id J K hJK
  have hmix := expectedDiagonalWard_mixture_abs_le (labeledCascadeLaw n b : Measure (LabeledTree n)) P
    ν (measurable_labeledSpinReference_general n π) H hH D₁ hm₁ D₂ hm₂
    (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalFreshCap_nonneg eig J K)
    (fun z => tensorDiagonalDirect_abs_le eig J K Prod.fst z.1.1 z.2)
    (fun z => tensorDiagonalFresh_abs_le eig J K Prod.fst z.1.1 z.2) hward
  rw [spinPriorReplicaAverage_cascade_mixture μ π eig c I degree amp n b treeDegree h hh h0
    (tensorDiagonalDirect eig J K Prod.fst) (measurable_tensorDiagonalDirect eig J K Prod.fst)
    (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalDirect_abs_le eig J K Prod.fst),
    spinPriorReplicaAverage_cascade_mixture μ π eig c I degree amp n b treeDegree h hh h0
    (tensorDiagonalFresh eig J K Prod.fst) (measurable_tensorDiagonalFresh eig J K Prod.fst)
    (tensorDiagonalFreshCap_nonneg eig J K) (tensorDiagonalFresh_abs_le eig J K Prod.fst)]
  exact hmix


end InvariantIsing

end

end OAI
