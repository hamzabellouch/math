import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalPrincipalObservables
import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalWardMeasurability
import OAI.Probability.InvariantIsing.Arrays.TensorPrincipalWard

namespace OAI

/-! The actual finite diagonal principal Ward bound in original-state
one- and two-replica form, uniform in the leaf restriction. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

def expectedDiagonalWard {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (ν : Measure X) (H : Ω × X → ℝ)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (D₂ : Ω × (Fin 2 → X) → ℝ) : ℝ :=
  (∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₁ (ω,σ)) ∂P) -
    ∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₂ (ω,σ)) ∂P

theorem expectedDiagonalWard_restriction_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (hD₁ : Measurable D₁)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ z, |D₁ z| ≤ B₁) (hb₂ : ∀ z, |D₂ z| ≤ B₂)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => expectedDiagonalWard P (normalizedRestriction ν (S n)) H D₁ D₂) atTop
      (𝓝 (expectedDiagonalWard P ν H D₁ D₂)) :=
  (expected_referenceReplicaMean_restriction_tendsto P ν H hH he D₁ hD₁ hB₁ hb₁ hS hexh hpos).sub
    (expected_referenceReplicaMean_restriction_tendsto P ν H hH he D₂ hD₂ hB₂ hb₂ hS hexh hpos)

theorem expectedDiagonalWard_abs_le_of_restriction {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (hD₁ : Measurable D₁)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ z, |D₁ z| ≤ B₁) (hb₂ : ∀ z, |D₂ z| ≤ B₂)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0)
    {ε : ℝ} (hfinite : ∀ n,
      |expectedDiagonalWard P (normalizedRestriction ν (S n)) H D₁ D₂| ≤ ε) :
    |expectedDiagonalWard P ν H D₁ D₂| ≤ ε :=
  le_of_tendsto (expectedDiagonalWard_restriction_tendsto P ν H hH he D₁ hD₁ D₂ hD₂
    hB₁ hB₂ hb₁ hb₂ hS hexh hpos).abs (Eventually.of_forall hfinite)

lemma expectedDiagonalWard_subtype {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) (ν : Measure X) [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν S ≠ 0)
    (H : Ω × X → ℝ) (D₁ : Ω × (Fin 1 → X) → ℝ) (D₂ : Ω × (Fin 2 → X) → ℝ) :
    expectedDiagonalWard P (subtypeReference ν S)
      (fun z : Ω × S => H (z.1,z.2))
      (fun z => D₁ (z.1, fun i => (z.2 i : X)))
      (fun z => D₂ (z.1, fun i => (z.2 i : X))) =
      expectedDiagonalWard P (normalizedRestriction ν S) H D₁ D₂ := by
  have he {r : ℕ} (z : Ω) (O : (Fin r → X) → ℝ) :
      referenceReplicaMean (subtypeReference ν S) (fun s => H (z,s))
        (fun σ => O (fun i => (σ i : X))) =
      referenceReplicaMean (normalizedRestriction ν S) (fun s => H (z,s)) O :=
    referenceReplicaMean_subtype hS hpos
      (measurable_of_countable (fun s => H (z,s))) (measurable_of_countable O)
  unfold expectedDiagonalWard
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun z => he z (fun σ => D₁ (z,σ))
  · apply integral_congr_ae
    exact ae_of_all _ fun z => he z (fun σ => D₂ (z,σ))

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma tensorRestrictionDiagonalVariation_principal_eq {N m k n : ℕ}
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
      tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s}) eig c I degree amplitude v x i j z =
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (tensorDiagonalDirect eig J K (fun s => (x s).1) z.1) -
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (tensorDiagonalFresh eig J K (fun s => (x s).1) z.1) := by
  have hcoord (i j : Fin N) : tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s})
      eig c I degree amplitude v x i j z =
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (fun σ : Fin 1 → S =>
          spinCoordinate (specialToOrthogonal z.1) (x (σ 0)).1 j ^ 2 -
            spinCoordinate (specialToOrthogonal z.1) (x (σ 0)).1 i ^ 2 +
            coordinateProduct i j (specialToOrthogonal z.1) (x (σ 0)).1 *
              ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal z.1) (x (σ 0)).1)) -
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (fun σ : Fin 2 → S => coordinateProduct i j (specialToOrthogonal z.1) (x (σ 0)).1 *
          ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal z.1) (x (σ 1)).1)) :=
    finiteGibbsVariation_reference ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
      (tensorRestrictionDiagonalObservable i j x z.1)
      (fun s => (eig i - eig j) * tensorRestrictionDiagonalObservable i j x z.1 s)
      (tensorRestrictionDiagonalVariation i j x z.1)
  simp_rw [hcoord]
  unfold tensorDiagonalDirect tensorDiagonalFresh
  rw [referenceReplicaMean_const_mul, referenceReplicaMean_const_mul]
  simp_rw [referenceReplicaMean_finite_finset_sum]
  simp only [Finset.sum_sub_distrib]
  ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma tensorRestriction_diagonal_integral_pair {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j)
    (hiW : Integrable (tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j)
      (μ.prod gaussianCoordinates)) :
    (∫ z, tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j z
      ∂μ.prod gaussianCoordinates) =
      -(∫ z, tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j z
        ∂μ.prod gaussianCoordinates) := by
  have hiV := integrable_tensorRestrictionDiagonalPrincipalVariation μ hw eig c I degree amplitude v x i j
  have he := tensorRestriction_diagonal_ward hN μ hw eig c I degree amplitude v x i j hij
  change (∫ U, (∫ g, tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j (U,g)
      ∂gaussianCoordinates) + ∫ g, tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j (U,g)
      ∂gaussianCoordinates ∂μ) = 0 at he
  rw [integral_add hiV.integral_prod_left hiW.integral_prod_left,
    ← integral_prod _ hiV, ← integral_prod _ hiW] at he
  linarith

lemma tensorRestrictionDiagonalVariation_principal_integral {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) :
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × S =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    expectedDiagonalWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2) =
      ∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s}) eig c I degree amp v x i j z
        ∂μ.prod gaussianCoordinates := by
  intro H
  let P := μ.prod gaussianCoordinates
  let V := fun i j : Fin N => tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s})
    eig c I degree amp v x i j
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v x s)
  let D₁ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 1 → S) =>
    tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → S) =>
    tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2
  have hm₁ : Measurable D₁ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalDirect_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalFresh_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  have hi₁ : Integrable (fun z => referenceReplicaMean ν (fun s => H (z,s)) (fun σ => D₁ (z,σ))) P :=
    integrable_finite_referenceReplicaMean P ν H hH D₁ hm₁ (tensorDiagonalDirectCap_nonneg eig J K)
      (fun z => tensorDiagonalDirect_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
  have hi₂ : Integrable (fun z => referenceReplicaMean ν (fun s => H (z,s)) (fun σ => D₂ (z,σ))) P :=
    integrable_finite_referenceReplicaMean P ν H hH D₂ hm₂ (tensorDiagonalFreshCap_nonneg eig J K)
      (fun z => tensorDiagonalFresh_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
  change expectedDiagonalWard P ν H D₁ D₂ = _
  unfold expectedDiagonalWard
  rw [← integral_sub hi₁ hi₂]
  apply integral_congr_ae
  exact ae_of_all _ fun z => (tensorRestrictionDiagonalVariation_principal_eq ν eig c I degree amp v x J K z).symm

/-- The actual finite diagonal Ward residual has a uniform quadratic
perturbation bound, with no limiting Ward assumption. -/
theorem tensorRestriction_diagonal_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 := fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × S =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedDiagonalWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2)| ≤
      48 * D * perturbationScale N ^ 2 := by
  intro amp v H
  let P := μ.prod gaussianCoordinates
  let w := fun s : S => ν.real {s}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  let V := fun i j : Fin N => tensorRestrictionDiagonalPrincipalVariation w eig c I degree amp v x i j
  let W := fun i j : Fin N => tensorRestrictionDiagonalCorrection w eig c I degree amp v x i j
  have hiV (i j : Fin N) : Integrable (V i j) P :=
    integrable_tensorRestrictionDiagonalPrincipalVariation μ hw eig c I degree amp v x i j
  have hiW (i j : Fin N) : Integrable (W i j) P :=
    integrable_tensorRestrictionDiagonalCorrection hN μ hw eig c I degree treeDegree u hu D hD hdegree
      h hh h0 x i j
  have hz (i : Fin N) (hi : i ∈ J) (j : Fin N) (hj : j ∈ K) :
      (∫ z, V i j z ∂P) = -(∫ z, W i j z ∂P) := by
    have hij : i ≠ j := fun he => (Finset.disjoint_left.mp hJK hi) (he.symm ▸ hj)
    exact tensorRestriction_diagonal_integral_pair hN μ hw eig c I degree amp v x i j hij (hiW i j)
  have hzero : (∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, V i j z ∂P) =
      -(∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z ∂P) :=
    normalized_integral_sum_eq_neg P J K V W hiV hiW hz
  have hprincipal := tensorRestrictionDiagonalVariation_principal_integral μ ν eig c I degree amp v x J K
  rw [hprincipal, hzero, abs_neg]
  have hb := norm_integral_le_of_norm_le_const (μ := P)
    (ae_of_all P fun z => show ‖(N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z‖ ≤
      48 * D * perturbationScale N ^ 2 from by
        rw [Real.norm_eq_abs]
        exact tensorRestriction_actualDiagonalWardCorrection_abs_le hN z.1 hw
          (tensorRestrictionHamiltonian eig c I degree amp v x z.1 z.2) I degree treeDegree u hu
          D hD hdegree h hh h0 J K x)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

end InvariantIsing

end

end OAI
