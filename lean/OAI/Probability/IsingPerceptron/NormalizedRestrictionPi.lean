import Mathlib
import OAI.Probability.IsingPerceptron.CountableMonomialGG
import OAI.Probability.IsingPerceptron.PartitionPowLe

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma normalizedRestriction_pi {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    (A : ι → Set X) (hA : ∀ i, ν (A i) ≠ 0) :
    Measure.pi (fun i => normalizedRestriction ν (A i)) =
      normalizedRestriction (Measure.pi (fun _ : ι => ν)) (Set.univ.pi A) := by
  classical
  have : ∀ i, IsProbabilityMeasure (normalizedRestriction ν (A i)) :=
    fun i => normalizedRestriction_probability (hA i)
  apply Measure.pi_eq
  intro S hS
  simp only [normalizedRestriction,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply (MeasurableSet.univ_pi hS),← Set.pi_inter_distrib]
  simp_rw [Measure.pi_pi,Measure.restrict_apply (hS _)]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (measure_ne_top _ _)),
    ← Finset.prod_mul_distrib]

lemma replica_restriction_mass_ne_zero {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    {A : Set X} (hA : ν A ≠ 0) :
    (Measure.pi (fun _ : ι => ν)) (Set.univ.pi (fun _ => A)) ≠ 0 := by
  rw [Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hA)

lemma replica_restriction_eventually {ι X : Type*} [Finite ι]
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (σ : ι → X) :
    ∀ᶠ n in atTop, σ ∈ Set.univ.pi (fun _ : ι => A n) := by
  filter_upwards [Filter.eventually_all.mpr (fun i => hA (σ i))] with n hn
  exact Set.mem_univ_pi.mpr hn

def subtypeReference {X : Type*} [MeasurableSpace X] (ν : Measure X) (A : Set X) : Measure A :=
  (ν A)⁻¹ • ν.comap Subtype.val

lemma subtypeReference_preserving {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {A : Set X} (hA : MeasurableSet A) :
    MeasurePreserving Subtype.val (subtypeReference ν A) (normalizedRestriction ν A) := by
  refine ⟨measurable_subtype_coe,?_⟩
  rw [subtypeReference,Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    map_comap_subtype_coe hA]
  rfl

lemma subtypeReference_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {A : Set X} (hA : MeasurableSet A) (hp : ν A ≠ 0) :
    IsProbabilityMeasure (subtypeReference ν A) := by
  have : IsProbabilityMeasure (normalizedRestriction ν A) := normalizedRestriction_probability hp
  have : IsProbabilityMeasure ((subtypeReference ν A).map Subtype.val) :=
    (subtypeReference_preserving ν hA).map_eq.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable

lemma referenceReplicaMean_subtype {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {A : Set X} (hA : MeasurableSet A) (hp : ν A ≠ 0)
    {H : X → ℝ} (hmH : Measurable H) {r : ℕ} {D : (Fin r → X) → ℝ} (hmD : Measurable D) :
    referenceReplicaMean (subtypeReference ν A) (fun x => H x)
      (fun σ => D (fun i => (σ i : X))) = referenceReplicaMean (normalizedRestriction ν A) H D := by
  have : IsProbabilityMeasure (subtypeReference ν A) := subtypeReference_probability ν hA hp
  have : IsProbabilityMeasure (normalizedRestriction ν A) := normalizedRestriction_probability hp
  exact referenceReplicaMean_map (subtypeReference_preserving ν hA) hmH hmD

lemma cylinder_replica_law {X : Type*} (a : X → ℕ →₀ ℝ) {r : ℕ} (σ : Fin r → X) :
    gaussianCoordinates.map (fun g => ∑ i, cylinderField (a (σ i)) g) =
      gaussianReal 0 (((∑ i, a (σ i)).sum (fun _ c => c^2)).toNNReal) := by
  have he : (fun g => ∑ i, cylinderField (a (σ i)) g) = cylinderField (∑ i, a (σ i)) := by
    funext g
    exact (cylinderField_finset_sum Finset.univ _ g).symm
  rw [he,cylinderField_law]

lemma cylinder_replica_variance_le {X : Type*} (a : X → ℕ →₀ ℝ) {K : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) {r : ℕ} (σ : Fin r → X) :
    ((((∑ i, a (σ i)).sum (fun _ c => c^2)).toNNReal : ℝ)) ≤ (r:ℝ)^2*K := by
  have hnonneg : 0 ≤ (∑ i, a (σ i)).sum (fun _ c => c^2) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Real.coe_toNNReal _ hnonneg]
  simpa only [Fintype.card_fin] using cylinder_variance_sum_le (fun i => a (σ i)) (fun i => ha (σ i))

theorem cylinder_replica_restriction_tendsto {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {ν : Measure X} [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    {r : ℕ} (D : (Fin r → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ g, referenceReplicaMean (normalizedRestriction ν (A n))
      (fun x => cylinderField (a x) g) D ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g) D ∂gaussianCoordinates)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (A n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin r → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have ht := gaussian_bounded_restriction_expectation_tendsto
    (ν := Measure.pi (fun _ : Fin r => ν)) hmH (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (cylinder_replica_variance_le a ha)
    (A := fun n => Set.univ.pi (fun _ : Fin r => A n))
    (fun _ => MeasurableSet.univ_pi (fun _ => Set.to_countable _ |>.measurableSet))
    (replica_restriction_eventually hA) (fun n => replica_restriction_mass_ne_zero (hpos n))
  simpa only [Function.comp_apply,referenceReplicaMean_eq_ratio,← normalizedRestriction_pi (fun _ : Fin r => A _)
    (fun _ => hpos _)] using ht

theorem cylinder_replica_insertion_restriction_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Measure X} [IsProbabilityMeasure ν] (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ g, referenceReplicaMean (normalizedRestriction ν (A n))
      (fun x => cylinderField (a x) g) (fun σ => cylinderField (b (σ 0)) g*D σ)
      ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
        (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (A n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmY : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) => cylinderField (b (z.2 0)) z.1) :=
    (measurable_cylinderFields b).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hv (σ : Fin (r+1) → X) : (((b (σ 0)).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ L := by
    have hnonneg : 0 ≤ (b (σ 0)).sum (fun _ c => c^2) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.coe_toNNReal _ hnonneg]
    exact hb (σ 0)
  have ht := gaussian_insertion_restriction_expectation_tendsto
    (ν := Measure.pi (fun _ : Fin (r+1) => ν)) hmH hmY
    (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (fun σ => cylinderField_law (b (σ 0)))
    (cylinder_replica_variance_le a ha) hv
    (A := fun n => Set.univ.pi (fun _ : Fin (r+1) => A n))
    (fun _ => MeasurableSet.univ_pi (fun _ => Set.to_countable _ |>.measurableSet))
    (replica_restriction_eventually hA) (fun n => replica_restriction_mass_ne_zero (hpos n))
  simpa only [Function.comp_apply,mul_assoc,referenceReplicaMean_eq_ratio,
    ← normalizedRestriction_pi (fun _ : Fin (r+1) => A _) (fun _ => hpos _)] using ht

lemma countable_reference_exhaustion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν] :
    ∃ A : ℕ → Set X, (∀ n, (A n).Finite) ∧ (∀ n, ν (A n) ≠ 0) ∧
      (∀ x, ∀ᶠ n in atTop, x ∈ A n) := by
  classical
  let := Encodable.ofCountable X
  have hx : ∃ x : X, ν {x} ≠ 0 := by
    by_contra! hn
    have hz : ν = 0 := Measure.ext_of_singleton (fun x => by simpa using hn x)
    have hu := measure_univ (μ := ν)
    simp only [hz, Measure.coe_zero, Pi.zero_apply] at hu
    exact zero_ne_one hu
  obtain ⟨x₀,hx₀⟩ := hx
  let A : ℕ → Set X := fun n => {x | Encodable.encode x ≤ n+Encodable.encode x₀}
  refine ⟨A,fun n => ?_,fun n => ?_,fun x => ?_⟩
  · exact (Set.finite_Iic _).preimage Encodable.encode_injective.injOn
  · intro hz
    apply hx₀
    exact measure_mono_null (fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Nat.le_add_left _ _) hz
  · filter_upwards [eventually_ge_atTop (Encodable.encode x)] with n hn
    exact hn.trans (Nat.le_add_right _ _)

lemma finite_restriction_cylinder_insertion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {ν : Measure X} [IsProbabilityMeasure ν]
    {A : Set X} (hA : A.Finite) (hp : ν A ≠ 0)
    (a b : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) :
    (∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  let := hA.fintype
  have hmA : MeasurableSet A := hA.measurableSet
  have : IsProbabilityMeasure (subtypeReference ν A) := subtypeReference_probability ν hmA hp
  have he {q : ℕ} (g : ℕ → ℝ) (F : (Fin q → X) → ℝ) :
      referenceReplicaMean (subtypeReference ν A) (fun x => cylinderField (a x) g)
        (fun σ => F (fun i => (σ i : X))) =
      referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g) F :=
    referenceReplicaMean_subtype hmA hp (H := fun x => cylinderField (a x) g)
      (D := F) (measurable_of_countable _) (measurable_of_countable _)
  have hi := finite_cylinder_reference_insertion (subtypeReference ν A)
    (fun x => a x) (fun x => b x) (fun σ => D (fun i => (σ i : X)))
  convert hi using 1
  · congr 1
    funext g
    exact (he g (fun σ => cylinderField (b (σ 0)) g*D σ)).symm
  · congr 1
    · congr 1
      funext g
      exact (he g (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i))))).symm
    · congr 1
      congr 1
      funext g
      exact (he g (fun τ : Fin (r+1+1) → X =>
        D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))).symm

theorem countable_cylinder_reference_insertion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  obtain ⟨A,hfin,hpos,hA⟩ := countable_reference_exhaustion ν
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      |cylinderCross (b x) (a y)| ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 :=
        abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B]; linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun i _ => hcross _ _)
      _ = (r+1 : ℕ)*B := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]
    exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]
    exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  have hleft := cylinder_replica_insertion_restriction_tendsto a b ha hb D hc hD hA hpos
  have hright₁ := cylinder_replica_restriction_tendsto a ha
    (fun σ : Fin (r+1) → X => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i))))
    (c := c*((r+1 : ℕ)*B)) (by positivity) hfirst hA hpos
  have hright₂ := cylinder_replica_restriction_tendsto a ha
    (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
    (c := c*B) (mul_nonneg hc hB) hfresh hA hpos
  apply tendsto_nhds_unique hleft
  exact (hright₁.sub (hright₂.const_mul ((r+1 : ℕ) : ℝ))).congr
    (fun n => (finite_restriction_cylinder_insertion (hfin n) (hpos n) a b D).symm)

lemma measurable_countable_measure_pi {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] (r : ℕ) :
    Measurable (fun ω => Measure.pi (fun _ : Fin r => ν ω)) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : Measure.pi (fun _ : Fin r => ν ω) s =
      ∑' σ : Fin r → X, (∏ i : Fin r, ν ω {σ i}) * Measure.dirac σ s := by
    rw [← Measure.sum_smul_dirac (Measure.pi (fun _ : Fin r => ν ω)),Measure.sum_apply _ hs]
    simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_singleton]
  simp_rw [he]
  apply Measurable.tsum
  intro σ
  exact (Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (measurableSet_singleton _)).comp hν)).mul_const _

lemma measurable_random_referencePartition {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) :
    Measurable (fun ω => referencePartition (ν ω) (fun x => H (ω,x))) := by
  let κ : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel κ := ⟨fun ω => by
    change IsProbabilityMeasure (ν ω)
    infer_instance⟩
  exact (hH.exp.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma measurable_random_referenceReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) {r : ℕ}
    {D : Ω × (Fin r → X) → ℝ} (hD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean (ν ω) (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  let κ : Kernel Ω (Fin r → X) := ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω),
    measurable_countable_measure_pi hν r⟩
  have : IsMarkovKernel κ := ⟨fun ω => by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω))
    infer_instance⟩
  have hm : Measurable (fun z : Ω × (Fin r → X) => Real.exp (∑ i, H (z.1,z.2 i))*D z) := by
    apply Measurable.mul _ hD
    apply Measurable.exp
    exact Finset.measurable_sum _ (fun i _ => hH.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((measurable_random_referencePartition hν hH).pow_const r)

lemma referenceReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    |referenceReplicaMean ν H D| ≤ c := by
  rw [referenceReplicaMean_eq_ratio]
  by_cases he : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))) (Measure.pi (fun _ => ν))
  · exact abs_bounded_gibbs_test_le he hmD hc hD
  · rw [integral_undef he,div_zero,abs_zero]
    exact hc

lemma integrable_of_measurable_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    {c : ℝ} (hbound : ∀ ω, |F ω| ≤ c) : Integrable F μ := by
  exact (integrable_const c).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)

lemma abs_integral_le_const_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    {c : ℝ} (hbound : ∀ ω, |F ω| ≤ c) : |∫ ω, F ω ∂μ| ≤ c := by
  calc
    _ ≤ ∫ ω, |F ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _, c ∂μ := integral_mono ((integrable_of_measurable_abs_le hF hbound).abs)
      (integrable_const _) hbound
    _ = c := by simp

lemma measurable_random_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2) D) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd))
    ((measurable_of_countable D).comp measurable_snd)

lemma integrable_random_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun ω => ∫ g, referenceReplicaMean (ν ω)
      (fun x => cylinderField (a x) g) D ∂gaussianCoordinates) P := by
  apply integrable_of_measurable_abs_le
    (measurable_random_cylinder_mean hν a D |>.stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  apply abs_integral_le_const_of_bound
    ((measurable_random_cylinder_mean hν a D).comp measurable_prodMk_left)
  intro g
  exact referenceReplicaMean_abs_le (ν ω) (fun x => cylinderField (a x) g)
    D (measurable_of_countable _) hc hD

theorem random_countable_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates ∂P) =
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates ∂P) -
    (r+1 : ℕ)*(∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates ∂P) := by
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      _ ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 := abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B]; linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      _ ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun _ _ => hcross _ _)
      _ = _ := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]; exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]; exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  simp_rw [countable_cylinder_reference_insertion _ a b ha hb D hc hD]
  rw [integral_sub (integrable_random_cylinder_mean hν a _ (by positivity) hfirst)
    ((integrable_random_cylinder_mean hν a _ (mul_nonneg hc hB) hfresh).const_mul _),integral_const_mul]

lemma joint_integrable_square_of_uniform_conditionals {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] {P : Measure Ω} {Q : Measure Γ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {F : Ω × Γ → ℝ}
    (hm : Measurable F) {C : ℝ}
    (hi : ∀ ω, Integrable (fun g => F (ω,g)^2) Q)
    (hb : ∀ ω, (∫ g, F (ω,g)^2 ∂Q) ≤ C) :
    Integrable (fun z => F z^2) (P.prod Q) := by
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  apply integrable_of_measurable_abs_le
    ((hm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact hb ω

lemma measurable_random_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ)) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  have hmD : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Fin (r+1) → X) =>
      cylinderField (b (p.2 0)) p.1.2*D p.2) :=
    ((measurable_cylinderFields b).comp
      (measurable_fst.snd.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
        ((measurable_of_countable D).comp measurable_snd)
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)) hmD

lemma cylinder_replica_insertion_second {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    let F := fun g => referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ)
    Integrable (fun g => F g^2) gaussianCoordinates ∧
      (∫ g, F g^2 ∂gaussianCoordinates) ≤
        c^2*((Real.exp (32*((r+1:ℕ):ℝ)^2*K)+2*Real.exp (32*L)+Real.exp (8*((r+1:ℕ):ℝ)^2*K))/2) := by
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmY : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) => cylinderField (b (z.2 0)) z.1) :=
    (measurable_cylinderFields b).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hv (σ : Fin (r+1) → X) : (((b (σ 0)).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ L := by
    have hnonneg : 0 ≤ (b (σ 0)).sum (fun _ c => c^2) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.coe_toNNReal _ hnonneg]
    exact hb (σ 0)
  have ht := gaussian_bounded_insertion_second
    (ν := Measure.pi (fun _ : Fin (r+1) => ν)) hmH hmY
    (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (fun σ => cylinderField_law (b (σ 0)))
    (cylinder_replica_variance_le a ha) hv
  simpa only [referenceReplicaMean_eq_ratio,mul_assoc,Function.comp_apply] using ht.2

theorem integrable_joint_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ)) (P.prod gaussianCoordinates) := by
  have hm := measurable_random_cylinder_insertion hν a b D
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_replica_insertion_second (ν ω) a b ha hb D hc hD).1)
    (fun ω => (cylinder_replica_insertion_second (ν ω) a b ha hb D hc hD).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

lemma integrable_exp_of_integer_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (hm : Measurable Y)
    (he : ∀ n : ℤ, Integrable (fun x => Real.exp ((n:ℝ)*Y x)) ν) (t : ℝ) :
    Integrable (fun x => Real.exp (t*Y x)) ν := by
  obtain ⟨n,hn⟩ := exists_nat_gt |t|
  have hp := he (n:ℤ)
  have hm' := he (-(n:ℤ))
  apply (hp.add hm').mono' (hm.const_mul t |>.exp.aestronglyMeasurable)
  refine ae_of_all _ fun x => ?_
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Int.cast_natCast,Int.cast_neg]
  by_cases hy : 0 ≤ Y x
  · have h : t*Y x ≤ (n:ℝ)*Y x := mul_le_mul_of_nonneg_right ((le_abs_self t).trans hn.le) hy
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have h : t*Y x ≤ -(n:ℝ)*Y x := mul_le_mul_of_nonpos_right (by linarith [neg_abs_le t]) (le_of_not_ge hy)
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

lemma random_cylinder_all_exp_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) :
    ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ t : ℝ,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
  let κ : Kernel (Ω × (ℕ → ℝ)) X := ⟨fun z => ν z.1,hν.comp measurable_fst⟩
  have : IsMarkovKernel κ := ⟨fun z => by
    change IsProbabilityMeasure (ν z.1)
    infer_instance⟩
  have hi (t : ℝ) : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
    have hm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
        Real.exp (t*cylinderField (a p.2) p.1.2)) :=
      ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t |>.exp
    have hs : MeasurableSet {z : Ω × (ℕ → ℝ) |
        Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1)} :=
      ProbabilityTheory.measurableSet_kernel_integrable (κ := κ) hm.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    refine ae_of_all _ fun ω => ?_
    have hv (x : X) : (((a x).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ K := by
      rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact ha x
    exact (gaussian_field_exp_integrable (ν := ν ω) (measurable_cylinderFields a)
      (fun x => cylinderField_law (a x)) hv t).1.prod_right_ae
  have hn : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ n : ℤ,
      Integrable (fun x => Real.exp ((n:ℝ)*cylinderField (a x) z.2)) (ν z.1) :=
    ae_all_iff.mpr (fun n => hi (n:ℝ))
  filter_upwards [hn] with z hz
  exact integrable_exp_of_integer_exp (measurable_of_countable _) hz

lemma measurable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) (t : ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact (measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    (((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t)).log

lemma cylinder_scaled_law {X : Type*} (a : X → ℕ →₀ ℝ) (x : X) (t : ℝ) :
    gaussianCoordinates.map (fun g => t*cylinderField (a x) g) =
      gaussianReal 0 (⟨t^2,sq_nonneg t⟩*(((a x).sum (fun _ c => c^2)).toNNReal)) := by
  have hm := measurable_cylinderField (a x)
  rw [show (fun g => t*cylinderField (a x) g) = (fun y : ℝ => t*y) ∘ cylinderField (a x) from rfl,
    ← Measure.map_map (by fun_prop) hm,cylinderField_law,gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 2

lemma cylinder_cgf_second {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun g => (cgf (fun x => cylinderField (a x) g) ν t)^2) gaussianCoordinates ∧
      (∫ g, (cgf (fun x => cylinderField (a x) g) ν t)^2 ∂gaussianCoordinates) ≤
        4*Real.exp (2*(t^2*K)) := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (a z.2) z.1) :=
    (measurable_cylinderFields a).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((a x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((a x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (ha x) (sq_nonneg _)
  exact gaussian_log_partition_second (ν := ν) hm (fun x => cylinder_scaled_law a x t) hv

lemma integrable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t)
      (P.prod gaussianCoordinates) := by
  have hm := measurable_random_cylinder_cgf hν a t
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).1)
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

lemma integrable_joint_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2) D) (P.prod gaussianCoordinates) := by
  exact integrable_of_measurable_abs_le (measurable_random_cylinder_mean hν a D)
    (fun z => referenceReplicaMean_abs_le (ν z.1) _ D (measurable_of_countable _) hc hD)

theorem joint_countable_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ) ∂P.prod gaussianCoordinates) =
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂P.prod gaussianCoordinates) -
    (r+1 : ℕ)*(∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂P.prod gaussianCoordinates) := by
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      _ ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 := abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B]; linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      _ ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun _ _ => hcross _ _)
      _ = _ := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]; exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]; exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  rw [integral_prod _ (integrable_joint_cylinder_insertion hν a b ha hb D hc hD),
    integral_prod _ (integrable_joint_cylinder_mean hν a _ (by positivity) hfirst),
    integral_prod _ (integrable_joint_cylinder_mean hν a _ (mul_nonneg hc hB) hfresh)]
  exact random_countable_cylinder_insertion hν a b ha hb D hc hD

end IsingPerceptron

end

end OAI
