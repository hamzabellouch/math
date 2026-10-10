import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalPrincipalWard
import OAI.Probability.InvariantIsing.Arrays.TensorCountableHamiltonian

namespace OAI

/-! The actual countable spin/leaf diagonal principal Ward bound. The finite
correction is removed before taking the leaf-exhaustion limit. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorFiniteRestriction_diagonal_principal_bound {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : X → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (S : Set X) (hSfin : S.Finite) (hSm : MeasurableSet S) (hpos : ν S ≠ 0) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
      fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedDiagonalWard (μ.prod gaussianCoordinates) (normalizedRestriction ν S) H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2)| ≤
      48 * D * perturbationScale N ^ 2 := by
  classical
  intro amp v H
  let := hSfin.fintype
  let νa := subtypeReference ν S
  have : IsProbabilityMeasure νa := subtypeReference_probability ν hSm hpos
  have hf := tensorRestriction_diagonal_principal_bound hN μ νa eig c I degree treeDegree u hu D hD
    hdegree h hh h0 (fun s : S => x s) J K hJK
  rw [← expectedDiagonalWard_subtype (μ.prod gaussianCoordinates) ν hSm hpos H]
  exact hf

theorem tensorCountable_diagonal_principal_bound {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : X → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
      fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedDiagonalWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2)| ≤
      48 * D * perturbationScale N ^ 2 := by
  classical
  intro amp v H
  let P := μ.prod gaussianCoordinates
  let D₁ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 1 → X) =>
    tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → X) =>
    tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v x s)
  have hm₁ : Measurable D₁ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalDirect_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalFresh_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  obtain ⟨S, hSfin, hSpos, hSexh⟩ := countable_reference_exhaustion ν
  have hSm (a : ℕ) : MeasurableSet (S a) := (hSfin a).measurableSet
  apply expectedDiagonalWard_abs_le_of_restriction P ν H hH
    (tensorCountableHamiltonian_exp_integrable_ae μ ν eig c I degree amp treeDegree h hh h0 x)
    D₁ hm₁ D₂ hm₂ (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalFreshCap_nonneg eig J K)
    (fun z => tensorDiagonalDirect_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
    (fun z => tensorDiagonalFresh_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
    hSm hSexh hSpos
  intro a
  exact tensorFiniteRestriction_diagonal_principal_bound hN μ ν eig c I degree treeDegree u hu D hD
    hdegree h hh h0 x J K hJK (S a) (hSfin a) (hSm a) (hSpos a)

end InvariantIsing

end

end OAI
