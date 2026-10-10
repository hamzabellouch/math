import OAI.Probability.InvariantIsing.Arrays.TensorCountableDiagonalWard
import OAI.Probability.InvariantIsing.Arrays.TensorCascadeReplicaAverage
import OAI.Probability.InvariantIsing.Arrays.CountableWardMixture

namespace OAI

/-! The actual enriched diagonal Ward residual, averaged over the cascade,
retains the uniform bound proved for every fixed countable reference. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem expectedDiagonalWard_mixture_abs_le {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ξ : Measure T) [IsProbabilityMeasure ξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (hD₁ : Measurable D₁)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ z, |D₁ z| ≤ B₁) (hb₂ : ∀ z, |D₂ z| ≤ B₂)
    {ε : ℝ} (hward : ∀ t, |expectedDiagonalWard P (ν t) H D₁ D₂| ≤ ε) :
    |(∫ t, (∫ ω, referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D₁ (ω,σ)) ∂P) ∂ ξ) -
      (∫ t, (∫ ω, referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D₂ (ω,σ)) ∂P) ∂ ξ)| ≤ ε := by
  have hi₁ := integrable_mixtureReplicaMean ξ P ν hν H hH D₁ hD₁ hB₁ hb₁
  have hi₂ := integrable_mixtureReplicaMean ξ P ν hν H hH D₂ hD₂ hB₂ hb₂
  rw [← integral_sub hi₁ hi₂]
  apply abs_integral_le_const_of_bound
    ((measurable_integral_mixtureReplicaMean P ν hν H hH D₁ hD₁).sub
      (measurable_integral_mixtureReplicaMean P ν hν H hH D₂ hD₂))
  exact hward

/-- The diagonal spectral Ward bound for the actual finite tensor-enriched
model, including all cascade, Haar and Gaussian averages. -/
theorem tensorNamespaced_diagonal_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    |tensorNamespacedReplicaAverage μ eig c I degree (tensorPerturbationAmplitude N u)
        n b treeDegree h (tensorDiagonalDirect eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      tensorNamespacedReplicaAverage μ eig c I degree (tensorPerturbationAmplitude N u)
        n b treeDegree h (tensorDiagonalFresh eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N))| ≤
      48 * D * perturbationScale N ^ 2 := by
  let amp := tensorPerturbationAmplitude N u
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun a => tensorPathProfile I degree n treeDegree h a
  let P := μ.prod gaussianCoordinates
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N))
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
    ν (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))) H hH D₁ hm₁ D₂ hm₂
    (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalFreshCap_nonneg eig J K)
    (fun z => tensorDiagonalDirect_abs_le eig J K Prod.fst z.1.1 z.2)
    (fun z => tensorDiagonalFresh_abs_le eig J K Prod.fst z.1.1 z.2) hward
  rw [tensorNamespacedReplicaAverage_cascade_mixture μ eig c I degree amp n b treeDegree h hh h0
    (tensorDiagonalDirect eig J K Prod.fst) (measurable_tensorDiagonalDirect eig J K Prod.fst)
    (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalDirect_abs_le eig J K Prod.fst),
    tensorNamespacedReplicaAverage_cascade_mixture μ eig c I degree amp n b treeDegree h hh h0
    (tensorDiagonalFresh eig J K Prod.fst) (measurable_tensorDiagonalFresh eig J K Prod.fst)
    (tensorDiagonalFreshCap_nonneg eig J K) (tensorDiagonalFresh_abs_le eig J K Prod.fst)]
  exact hmix

end InvariantIsing

end

end OAI
