import OAI.Probability.InvariantIsing.Arrays.TensorPrincipalObservables
import OAI.Probability.InvariantIsing.Arrays.TensorWardMeasurability
import OAI.Probability.InvariantIsing.Arrays.CountableWardFunctional

namespace OAI

/-! A finite normalized principal Ward residual bound. The exact Gaussian
correction is eliminated before countable leaf exhaustion. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S ι : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma referenceReplicaMean_finite_finset_sum (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) {r : ℕ} (t : Finset ι) (D : ι → (Fin r → S) → ℝ) :
    referenceReplicaMean ν H (fun σ => ∑ i ∈ t, D i σ) =
      ∑ i ∈ t, referenceReplicaMean ν H (D i) := by
  simp only [referenceReplicaMean_finiteGibbs, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma finiteGibbsVariation_pair_scaled_reference (ν : Measure S) [IsProbabilityMeasure ν]
    (H P : S → ℝ) (O dO : S → S → ℝ) (δ : ℝ) :
    finiteGibbsVariation (fun p : S × S => ν.real {p.1} * ν.real {p.2})
      (fun p => H p.1 + H p.2) (fun p => O p.1 p.2)
      (fun p => δ * (P p.1 + P p.2)) (fun p => dO p.1 p.2) =
      referenceReplicaMean ν H (fun σ : Fin 2 → S =>
        dO (σ 0) (σ 1) + O (σ 0) (σ 1) * (δ * (P (σ 0) + P (σ 1)))) -
      2 * referenceReplicaMean ν H (fun σ : Fin 3 → S => O (σ 0) (σ 1) * (δ * P (σ 2))) := by
  have he : (fun p : S × S => δ * (P p.1 + P p.2)) = fun p => δ * P p.1 + δ * P p.2 := by
    funext p
    ring
  rw [he, finiteGibbsVariation_pair_reference ν H (fun s => δ * P s) O dO]
  congr 2
  funext σ
  ring

lemma tensorRestrictionOffVariation_principal_eq {N m k n : ℕ}
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ)
    (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, finiteGibbsVariation
      (fun p : S × S => ν.real {p.1} * ν.real {p.2})
      (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
      (tensorRestrictionOffObservable i j F x z.1) (tensorRestrictionMainVariation eig i j x z.1)
      (tensorRestrictionOffVariation i j F x z.1) =
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (tensorOffDirect eig J K (fun s => (x s).1) F z.1) -
      2 * referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (tensorOffFresh eig J K (fun s => (x s).1) F z.1) := by
  have hH : tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2 =
      fun p => tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2 p.1 +
        tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2 p.2 :=
    funext (tensorRestrictionPairHamiltonian_eq eig c I degree amplitude v x z.1 z.2)
  have hcoord (i j : Fin N) : finiteGibbsVariation
      (fun p : S × S => ν.real {p.1} * ν.real {p.2})
      (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
      (tensorRestrictionOffObservable i j F x z.1) (tensorRestrictionMainVariation eig i j x z.1)
      (tensorRestrictionOffVariation i j F x z.1) =
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (fun σ : Fin 2 → S =>
          offCoordinateVariation i j F (specialToOrthogonal z.1) ((x (σ 0)).1, (x (σ 1)).1) +
          offCoordinateProduct i j F (specialToOrthogonal z.1) ((x (σ 0)).1, (x (σ 1)).1) *
            ((eig i - eig j) * (coordinateProduct i j (specialToOrthogonal z.1) (x (σ 0)).1 +
              coordinateProduct i j (specialToOrthogonal z.1) (x (σ 1)).1))) -
      2 * referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (fun σ : Fin 3 → S =>
          offCoordinateProduct i j F (specialToOrthogonal z.1) ((x (σ 0)).1, (x (σ 1)).1) *
            ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal z.1) (x (σ 2)).1)) := by
    rw [hH]
    exact finiteGibbsVariation_pair_scaled_reference ν
      (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
      (fun s => coordinateProduct i j (specialToOrthogonal z.1) (x s).1)
      (fun s t => offCoordinateProduct i j F (specialToOrthogonal z.1) ((x s).1, (x t).1))
      (fun s t => offCoordinateVariation i j F (specialToOrthogonal z.1) ((x s).1, (x t).1)) (eig i - eig j)
  simp_rw [hcoord]
  unfold tensorOffDirect tensorOffFresh
  rw [referenceReplicaMean_const_mul, referenceReplicaMean_const_mul]
  simp_rw [referenceReplicaMean_finite_finset_sum]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma integral_normalized_double_sum {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (J K : Finset (Fin N)) (f : Fin N → Fin N → Ω → ℝ)
    (hf : ∀ i j, Integrable (f i j) P) :
    (∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, f i j z ∂P) =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, ∫ z, f i j z ∂P := by
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (fun j _ => hf i j)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma normalized_integral_sum_eq_neg {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (J K : Finset (Fin N)) (V W : Fin N → Fin N → Ω → ℝ)
    (hiV : ∀ i j, Integrable (V i j) P) (hiW : ∀ i j, Integrable (W i j) P)
    (hz : ∀ i ∈ J, ∀ j ∈ K, (∫ z, V i j z ∂P) = -(∫ z, W i j z ∂P)) :
    (∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, V i j z ∂P) =
      -(∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z ∂P) := by
  rw [integral_normalized_double_sum P J K V hiV, integral_normalized_double_sum P J K W hiW]
  calc
    _ = (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, -(∫ z, W i j z ∂P) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hz i hi j hj
    _ = _ := by simp only [Finset.sum_neg_distrib, mul_neg]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
def tensorRestrictionOffPrincipalVariation {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  finiteGibbsVariation (fun p : S × S => w p.1 * w p.2)
    (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionOffObservable i j F x z.1) (tensorRestrictionMainVariation eig i j x z.1)
    (tensorRestrictionOffVariation i j F x z.1)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma tensorRestriction_off_integral_pair {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B)
    (hiW : Integrable (tensorRestrictionOffCorrection w eig c I degree amplitude v x i j F)
      (μ.prod gaussianCoordinates)) :
    (∫ z, tensorRestrictionOffPrincipalVariation w eig c I degree amplitude v x i j F z
      ∂μ.prod gaussianCoordinates) =
      -(∫ z, tensorRestrictionOffCorrection w eig c I degree amplitude v x i j F z
        ∂μ.prod gaussianCoordinates) := by
  have hiV : Integrable (tensorRestrictionOffPrincipalVariation w eig c I degree amplitude v x i j F)
      (μ.prod gaussianCoordinates) :=
    integrable_tensorRestrictionOffVariation μ hw eig c I degree amplitude v x i j F B hB hF
  have he := tensorRestriction_off_ward hN μ hw eig c I degree amplitude v x i j hij F B hB hF
  change (∫ U, (∫ g, tensorRestrictionOffPrincipalVariation w eig c I degree amplitude v x i j F (U,g)
      ∂gaussianCoordinates) +
    ∫ g, tensorRestrictionOffCorrection w eig c I degree amplitude v x i j F (U,g)
      ∂gaussianCoordinates ∂μ) = 0 at he
  rw [integral_add hiV.integral_prod_left hiW.integral_prod_left,
    ← integral_prod _ hiV, ← integral_prod _ hiW] at he
  linarith

lemma integrable_finite_referenceReplicaMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure S) [IsProbabilityMeasure ν]
    (H : Ω × S → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → S) → ℝ) (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z, |D z| ≤ C) :
    Integrable (fun ω => referenceReplicaMean ν (fun s => H (ω,s)) (fun σ => D (ω,σ))) P :=
  integrable_of_measurable_abs_le (measurable_random_referenceReplicaMean measurable_const hH hD)
    (fun ω => referenceReplicaMean_abs_le ν _ _ (measurable_of_countable _) hC (fun σ => hb (ω,σ)))

lemma tensorRestrictionOffVariation_principal_integral {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B) :
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × S =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    expectedReplicaWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorOffDirect eig J K (fun s => (x s).1) F z.1.1 z.2)
      (fun z => tensorOffFresh eig J K (fun s => (x s).1) F z.1.1 z.2) =
      ∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        tensorRestrictionOffPrincipalVariation (fun s => ν.real {s}) eig c I degree amp v x i j F z
        ∂μ.prod gaussianCoordinates := by
  intro H
  let P := μ.prod gaussianCoordinates
  let V := fun i j : Fin N => tensorRestrictionOffPrincipalVariation (fun s => ν.real {s})
    eig c I degree amp v x i j F
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v x s)
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → S) =>
    tensorOffDirect eig J K (fun s => (x s).1) F z.1.1 z.2
  let D₃ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 3 → S) =>
    tensorOffFresh eig J K (fun s => (x s).1) F z.1.1 z.2
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorOffDirect_at eig J K (fun s => (x s).1) F σ).comp measurable_fst)
  have hm₃ : Measurable D₃ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorOffFresh_at eig J K (fun s => (x s).1) F σ).comp measurable_fst)
  have hi₂ : Integrable (fun z => referenceReplicaMean ν (fun s => H (z,s)) (fun σ => D₂ (z,σ))) P :=
    integrable_finite_referenceReplicaMean P ν H hH D₂ hm₂ (tensorOffDirectCap_nonneg eig J K hB)
      (fun z => tensorOffDirect_abs_le eig J K (fun s => (x s).1) F hB hF z.1.1 z.2)
  have hi₃ : Integrable (fun z => referenceReplicaMean ν (fun s => H (z,s)) (fun σ => D₃ (z,σ))) P :=
    integrable_finite_referenceReplicaMean P ν H hH D₃ hm₃ (tensorOffFreshCap_nonneg eig J K hB)
      (fun z => tensorOffFresh_abs_le eig J K (fun s => (x s).1) F hB hF z.1.1 z.2)
  have hprincipal : expectedReplicaWard P ν H D₂ D₃ =
      ∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, V i j z ∂P := by
    unfold expectedReplicaWard
    rw [← integral_const_mul, ← integral_sub hi₂ (hi₃.const_mul 2)]
    apply integral_congr_ae
    exact ae_of_all _ fun z => (tensorRestrictionOffVariation_principal_eq ν eig c I degree amp v x J K F z).symm
  exact hprincipal

/-- For the actual finite-prior tensor model, the principal Ward residual
is bounded by the Gaussian correction. The direct
and fresh observables use the original state prior and a generic spin
projection, so they survive countable leaf restriction unchanged. -/
theorem tensorRestriction_off_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 := fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × S =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedReplicaWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorOffDirect eig J K (fun s => (x s).1) F z.1.1 z.2)
      (fun z => tensorOffFresh eig J K (fun s => (x s).1) F z.1.1 z.2)| ≤
      192 * B * D * perturbationScale N ^ 2 := by
  intro amp v H
  let P := μ.prod gaussianCoordinates
  let w := fun s : S => ν.real {s}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  let V := fun i j : Fin N => tensorRestrictionOffPrincipalVariation w eig c I degree amp v x i j F
  let W := fun i j : Fin N => tensorRestrictionOffCorrection w eig c I degree amp v x i j F
  have hiV (i j : Fin N) : Integrable (V i j) P :=
    integrable_tensorRestrictionOffVariation μ hw eig c I degree amp v x i j F B hB hF
  have hiW (i j : Fin N) : Integrable (W i j) P :=
    integrable_tensorRestrictionOffCorrection hN μ hw eig c I degree treeDegree u hu D hD hdegree
      h hh h0 x i j F B hB hF
  have hz (i : Fin N) (hi : i ∈ J) (j : Fin N) (hj : j ∈ K) :
      (∫ z, V i j z ∂P) = -(∫ z, W i j z ∂P) := by
    have hij : i ≠ j := fun he => (Finset.disjoint_left.mp hJK hi) (he.symm ▸ hj)
    exact tensorRestriction_off_integral_pair hN μ hw eig c I degree amp v x i j hij F B hB hF (hiW i j)
  have hzero : (∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, V i j z ∂P) =
      -(∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z ∂P) :=
    normalized_integral_sum_eq_neg P J K V W hiV hiW hz
  have hprincipal := tensorRestrictionOffVariation_principal_integral μ ν eig c I degree amp v x
    J K F B hB hF
  rw [hprincipal, hzero, abs_neg]
  have hb := norm_integral_le_of_norm_le_const (μ := P)
    (ae_of_all P fun z => show ‖(N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z‖ ≤
      192 * B * D * perturbationScale N ^ 2 from by
        rw [Real.norm_eq_abs]
        exact tensorRestriction_actualWardCorrection_abs_le hN z.1 hw
          (tensorRestrictionPairHamiltonian eig c I degree amp v x z.1 z.2) I degree treeDegree u hu
          D hD hdegree h hh h0 J K F B hB hF x)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

end InvariantIsing

end

end OAI
