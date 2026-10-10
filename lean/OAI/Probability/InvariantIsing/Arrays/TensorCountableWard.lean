import OAI.Probability.InvariantIsing.Arrays.TensorPrincipalWard
import OAI.Probability.InvariantIsing.Arrays.TensorCountableHamiltonian
import OAI.Probability.InvariantIsing.Arrays.CountableWardSubtype

namespace OAI

/-! The actual countable spin/leaf principal Ward bound. The finite
correction is removed before taking the leaf-exhaustion limit. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorFiniteRestriction_off_principal_bound {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : X → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B)
    (S : Set X) (hSfin : S.Finite) (hSm : MeasurableSet S) (hpos : ν S ≠ 0) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
      fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedReplicaWard (μ.prod gaussianCoordinates) (normalizedRestriction ν S) H
      (fun z => tensorOffDirect eig J K (fun s => (x s).1) F z.1.1 z.2)
      (fun z => tensorOffFresh eig J K (fun s => (x s).1) F z.1.1 z.2)| ≤
      192 * B * D * perturbationScale N ^ 2 := by
  classical
  intro amp v H
  let := hSfin.fintype
  let νa := subtypeReference ν S
  have : IsProbabilityMeasure νa := subtypeReference_probability ν hSm hpos
  have hf := tensorRestriction_off_principal_bound hN μ νa eig c I degree treeDegree u hu D hD
    hdegree h hh h0 (fun s : S => x s) J K hJK F B hB hF
  rw [← expectedReplicaWard_subtype (μ.prod gaussianCoordinates) ν hSm hpos H]
  exact hf

theorem tensorCountable_off_principal_bound {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : X → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
      fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedReplicaWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorOffDirect eig J K (fun s => (x s).1) F z.1.1 z.2)
      (fun z => tensorOffFresh eig J K (fun s => (x s).1) F z.1.1 z.2)| ≤
      192 * B * D * perturbationScale N ^ 2 := by
  classical
  intro amp v H
  let P := μ.prod gaussianCoordinates
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → X) =>
    tensorOffDirect eig J K (fun s => (x s).1) F z.1.1 z.2
  let D₃ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 3 → X) =>
    tensorOffFresh eig J K (fun s => (x s).1) F z.1.1 z.2
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v x s)
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorOffDirect_at eig J K (fun s => (x s).1) F σ).comp measurable_fst)
  have hm₃ : Measurable D₃ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorOffFresh_at eig J K (fun s => (x s).1) F σ).comp measurable_fst)
  obtain ⟨S, hSfin, hSpos, hSexh⟩ := countable_reference_exhaustion ν
  have hSm (a : ℕ) : MeasurableSet (S a) := (hSfin a).measurableSet
  apply expectedReplicaWard_abs_le_of_restriction P ν H hH
    (tensorCountableHamiltonian_exp_integrable_ae μ ν eig c I degree amp treeDegree h hh h0 x)
    D₂ hm₂ D₃ hm₃ (tensorOffDirectCap_nonneg eig J K hB) (tensorOffFreshCap_nonneg eig J K hB)
    (fun z => tensorOffDirect_abs_le eig J K (fun s => (x s).1) F hB hF z.1.1 z.2)
    (fun z => tensorOffFresh_abs_le eig J K (fun s => (x s).1) F hB hF z.1.1 z.2)
    hSm hSexh hSpos
  intro a
  exact tensorFiniteRestriction_off_principal_bound hN μ ν eig c I degree treeDegree u hu D hD
    hdegree h hh h0 x J K hJK F B hB hF (S a) (hSfin a) (hSm a) (hSpos a)

end InvariantIsing

end

end OAI
