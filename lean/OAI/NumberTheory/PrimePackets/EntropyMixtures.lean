import Mathlib
import OAI.NumberTheory.PrimePackets.ShannonEntropy

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
namespace PrimeDegreePackets

lemma negMulLog_sum_le {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Real.negMulLog (∑ i, p i) ≤ ∑ i, Real.negMulLog (p i) := by
  rw [Real.negMulLog, ← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases h0 : p i = 0
  · simp [h0]
  have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm h0)
  have hs : p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  exact mul_le_mul_of_nonpos_left (Real.log_le_log hi hs) (neg_nonpos.mpr (hp i))

lemma finiteShannon_mixture_joint {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p : ι → α → ℝ) (hp1 : ∀ i, ∑ a, p i a = 1) :
    finiteShannon (fun z : ι × α => w z.1*p z.1 z.2) =
      finiteShannon w + ∑ i, w i*finiteShannon (p i) := by
  simp only [finiteShannon, Fintype.sum_prod_type, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp1, one_mul]

lemma finiteShannon_mixture_bounds {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p : ι → α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hp : ∀ i a, 0 ≤ p i a) (hp1 : ∀ i, ∑ a, p i a = 1) :
    (∑ i, w i*finiteShannon (p i)) ≤ finiteShannon (fun a => ∑ i, w i*p i a) ∧
    finiteShannon (fun a => ∑ i, w i*p i a) ≤
      finiteShannon w + ∑ i, w i*finiteShannon (p i) := by
  constructor
  · simp only [finiteShannon, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro a _
    exact Real.concaveOn_negMulLog.le_map_sum (fun i _ => hw i) hw1 (fun i _ => hp i a)
  · rw [← finiteShannon_mixture_joint w p hp1]
    simp only [finiteShannon, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun a _ => negMulLog_sum_le _ (fun i => mul_nonneg (hw i) (hp i a)))

lemma observationEntropy_finite_mixture_bounds {Y ι α : Type*} [MeasurableSpace Y]
    [Fintype ι] [Fintype α] (μ : Measure Y) [IsProbabilityMeasure μ]
    (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hmix : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    (∑ i, w i*observationEntropy (ν i) P) ≤ observationEntropy μ P ∧
    observationEntropy μ P ≤ finiteShannon w + ∑ i, w i*observationEntropy (ν i) P := by
  have heq a : μ.real {y | P y = a} = ∑ i, w i*(ν i).real {y | P y = a} := by
    rw [hmix]
    simp only [measureReal_def, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw _)]
  simpa only [observationEntropy, heq] using finiteShannon_mixture_bounds w
    (fun i a => (ν i).real {y | P y = a}) hw hw1 (fun i a => measureReal_nonneg)
    (fun i => observation_distribution_sum (ν i) P hP)

 

theorem observationEntropyRate_finite_mixture {Y ι α : Type*} [MeasurableSpace Y]
    [Fintype ι] [Fintype α] (μ : Measure Y) [IsProbabilityMeasure μ]
    (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hmix : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hTν : ∀ i, MeasurePreserving T (ν i) (ν i))
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ T P = ∑ i, w i*observationEntropyRate (ν i) T P := by
  have hleft := tendsto_observationEntropyRate μ hT P hP
  have hright : Tendsto (fun N : ℕ => ∑ i, w i*(observationEntropy (ν i) (orbitName T P N)/(N:ℝ)))
      atTop (𝓝 (∑ i, w i*observationEntropyRate (ν i) T P)) :=
    tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul (tendsto_observationEntropyRate (ν i) (hTν i) P hP))
  have hzero : Tendsto (fun N : ℕ => finiteShannon w / (N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : ∀ᶠ N : ℕ in atTop,
      (∑ i, w i*(observationEntropy (ν i) (orbitName T P N)/(N:ℝ))) ≤
        observationEntropy μ (orbitName T P N)/(N:ℝ) := by
    filter_upwards [] with N
    have H := (observationEntropy_finite_mixture_bounds μ ν w hw hw1 hmix
      (orbitName T P N) (orbitName_measurable_fiber hT.measurable hP N)).1
    simpa only [Finset.sum_div, mul_div_assoc] using div_le_div_of_nonneg_right H (Nat.cast_nonneg N)
  have hup : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName T P N)/(N:ℝ) ≤
        finiteShannon w/(N:ℝ)+(∑ i, w i*(observationEntropy (ν i) (orbitName T P N)/(N:ℝ))) := by
    filter_upwards [] with N
    have H := (observationEntropy_finite_mixture_bounds μ ν w hw hw1 hmix
      (orbitName T P N) (orbitName_measurable_fiber hT.measurable hP N)).2
    simpa only [add_div, Finset.sum_div, mul_div_assoc] using div_le_div_of_nonneg_right H (Nat.cast_nonneg N)
  apply le_antisymm
  · simpa only [zero_add] using le_of_tendsto_of_tendsto hleft (hzero.add hright) hup
  · exact le_of_tendsto_of_tendsto hright hleft hlo

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Filter Set
namespace PrimeDegreePackets

lemma kernel_comp_real {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) (κ : Kernel Z Y) [IsMarkovKernel κ]
    {S : Set Y} (hS : MeasurableSet S) :
    (κ ∘ₘ τ).real S = ∫ z, (κ z).real S ∂τ := by
  rw [measureReal_def, Measure.bind_apply hS κ.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hS).aemeasurable
    (ae_of_all _ fun z => measure_lt_top (κ z) S)).symm

lemma kernel_mixture_preserving {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) (κ : Kernel Z Y) {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z)) :
    MeasurePreserving T (κ ∘ₘ τ) (κ ∘ₘ τ) := by
  refine ⟨hT,?_⟩
  rw [Measure.map_comp τ κ hT]
  apply Measure.comp_congr
  filter_upwards [hκ] with z hz
  simpa only [Kernel.map_apply _ hT] using hz.map_eq

variable {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]

 

def kernelCell (τ : Measure Z) (κ : Kernel Z Y) (Q : Z → ι) (i : ι) : Measure Y :=
  if τ {z | Q z = i} = 0 then κ ∘ₘ τ else κ ∘ₘ cond τ {z | Q z = i}

instance kernelCell_probability (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (Q : Z → ι) (i : ι) :
    IsProbabilityMeasure (kernelCell τ κ Q i) := by
  unfold kernelCell
  split_ifs with h
  · infer_instance
  · have := cond_isProbabilityMeasure h
    infer_instance

lemma kernelCell_preserving (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) (Q : Z → ι) (i : ι)
    {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z)) :
    MeasurePreserving T (kernelCell τ κ Q i) (kernelCell τ κ Q i) := by
  unfold kernelCell
  split_ifs
  · exact kernel_mixture_preserving τ κ hT hκ
  · exact kernel_mixture_preserving _ κ hT (cond_absolutelyContinuous.ae_le hκ)

lemma weighted_kernelCell (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) (Q : Z → ι) (i : ι) :
    ENNReal.ofReal (τ.real {z | Q z = i}) • kernelCell τ κ Q i =
      κ ∘ₘ τ.restrict {z | Q z = i} := by
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  unfold kernelCell
  split_ifs with h
  · rw [h, zero_smul, Measure.restrict_eq_zero.mpr h]
    simp
  · rw [ProbabilityTheory.cond, Measure.comp_smul, smul_smul, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

lemma kernel_finite_cells [Fintype ι] (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) (Q : Z → ι) (hQ : ∀ i, MeasurableSet {z | Q z = i}) :
    κ ∘ₘ τ = ∑ i, ENNReal.ofReal (τ.real {z | Q z = i}) • kernelCell τ κ Q i := by
  simp_rw [weighted_kernelCell]
  have hτ : τ = ∑ i, τ.restrict {z | Q z = i} := by
    have hd : Pairwise (fun i j => Disjoint {z | Q z = i} {z | Q z = j}) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hz hz'
      exact hij (hz.symm.trans hz')
    have HU : (⋃ i, {z | Q z = i}) = (Set.univ : Set Z) := by ext; simp
    have H := τ.restrict_iUnion hd hQ
    rw [HU, Measure.restrict_univ] at H
    simpa only [Measure.sum_fintype] using H
  conv_lhs => rw [hτ]
  generalize (Finset.univ : Finset ι) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Measure.comp_add, ih]

lemma kernelCell_real (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (Q : Z → ι) (i : ι)
    (h : τ {z | Q z = i} ≠ 0) {S : Set Y} (hS : MeasurableSet S) :
    (kernelCell τ κ Q i).real S =
      (τ.real {z | Q z = i})⁻¹ * ∫ z in {z | Q z = i}, (κ z).real S ∂τ := by
  rw [kernelCell, ite_eq_right h, kernel_comp_real _ _ hS, ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, measureReal_def]

lemma measurable_kernel_real (κ : Kernel Z Y) {S : Set Y} (hS : MeasurableSet S) :
    Measurable (fun z => (κ z).real S) := (κ.measurable_coe hS).ennreal_toReal

lemma integrable_kernel_real (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] {S : Set Y} (hS : MeasurableSet S) :
    Integrable (fun z => (κ z).real S) τ := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (measurable_kernel_real κ hS).aestronglyMeasurable ?_
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

end PrimeDegreePackets


namespace PrimeDegreePackets

 

lemma finite_measurable_small_fibers {Z V : Type*} [MeasurableSpace Z]
    [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V]
    (p : Z → V) (hp : Measurable p) {K : Set V} (hK : IsCompact K)
    (hpK : ∀ z, p z ∈ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∃ Q : Z → (Fin k → Bool),
      (∀ i, MeasurableSet {z | Q z = i}) ∧
      ∀ z z', Q z = Q z' → dist (p z) (p z') < δ := by
  let U : V → Set V := fun v => Metric.ball v (δ/2)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U (fun _ => Metric.isOpen_ball) (by
    intro v _
    exact Set.mem_iUnion.mpr ⟨v, Metric.mem_ball_self (by positivity)⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let Q : Z → (Fin (Fintype.card s) → Bool) := fun z i => if p z ∈ U (e i) then true else false
  have hQ : Measurable Q := measurable_pi_iff.mpr fun i =>
    Measurable.ite (hp (Metric.isOpen_ball.measurableSet)) measurable_const measurable_const
  refine ⟨Fintype.card s,Q,fun i => hQ (measurableSet_singleton i),?_⟩
  intro z z' H
  obtain ⟨v,hv,hz⟩ := Set.mem_iUnion₂.mp (hs (hpK z))
  let i : Fin (Fintype.card s) := e.symm ⟨v,hv⟩
  have hzi : p z ∈ U (e i) := by simpa [i] using hz
  have hz'i : p z' ∈ U (e i) := by
    have H' := congrFun H i
    by_contra hn
    simp only [Q, ite_eq_left hzi, ite_eq_right hn] at H'
    contradiction
  have hz1 : dist (p z) (e i).val < δ/2 := hzi
  have hz2 : dist (p z') (e i).val < δ/2 := hz'i
  have Htri := dist_triangle (p z) (e i).val (p z')
  rw [dist_comm (e i).val (p z')] at Htri
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma continuous_finiteShannon {α : Type*} [Fintype α] :
    Continuous (finiteShannon (α := α)) := by
  unfold finiteShannon
  exact continuous_finsetSum _ (fun a _ => Real.continuous_negMulLog.comp (continuous_apply a))

lemma measurable_kernel_entropy {Z Y α : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [Fintype α] (κ : Kernel Z Y) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Measurable (fun z => observationEntropy (κ z) P) := by
  exact continuous_finiteShannon.measurable.comp (measurable_pi_iff.mpr
    (fun a => measurable_kernel_real κ (hP a)))

lemma integrable_kernel_entropy {Z Y α : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [Fintype α] (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Integrable (fun z => observationEntropy (κ z) P) τ := by
  apply Integrable.mono' (integrable_const (Real.log (Fintype.card α)))
    (measurable_kernel_entropy κ P hP).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (observationEntropy_nonneg (κ z) P hP)]
    exact finiteShannon_le_log_card (fun a => measureReal_nonneg)
      (observation_distribution_sum (κ z) P hP)

lemma ae_nonnull_fiber {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) (Q : Z → ι) :
    ∀ᵐ z ∂τ, τ {z' | Q z' = Q z} ≠ 0 := by
  have H (i : ι) : ∀ᵐ z ∂τ, Q z = i → τ {z' | Q z' = i} ≠ 0 := by
    by_cases hi : τ {z' | Q z' = i} = 0
    · apply ae_iff.mpr
      simp only [hi, ne_eq, not_true_eq_false, imp_false, not_not]
    · exact ae_of_all _ (fun _ _ => hi)
  filter_upwards [ae_all_iff.mpr H] with z hz
  exact hz (Q z) rfl

 

lemma kernelCell_real_close {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Kernel Z Y) [IsMarkovKernel κ]
    (Q : Z → ι) (hQ : ∀ i, MeasurableSet {z | Q z = i})
    {S : Set Y} (hS : MeasurableSet S) {δ : ℝ}
    (hclose : ∀ z z', Q z = Q z' → |(κ z).real S - (κ z').real S| ≤ δ)
    (z : Z) (hz : τ {z' | Q z' = Q z} ≠ 0) :
    |(kernelCell τ κ Q (Q z)).real S - (κ z).real S| ≤ δ := by
  let A := {z' | Q z' = Q z}
  have hw : 0 < τ.real A := ENNReal.toReal_pos hz (measure_ne_top _ _)
  have hAreal : (τ.restrict A).real Set.univ = τ.real A := by simp [measureReal_def]
  rw [kernelCell_real τ κ Q (Q z) hz hS, abs_le]
  have hlo : (κ z).real S - δ ≤
      (τ.real A)⁻¹ * ∫ z' in A, (κ z').real S ∂τ := by
    have H : ∫ z' in A, (κ z).real S-δ ∂τ ≤ ∫ z' in A, (κ z').real S ∂τ :=
      setIntegral_mono_on (integrable_const _).integrableOn
        (integrable_kernel_real τ κ hS).integrableOn (hQ (Q z)) (by
          intro z' hz'
          have := (abs_le.mp (hclose z' z hz')).1
          linarith)
    rw [integral_const] at H
    simp only [hAreal, smul_eq_mul] at H
    have := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hw.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using this
  have hup : (τ.real A)⁻¹ * ∫ z' in A, (κ z').real S ∂τ ≤ (κ z).real S+δ := by
    have H : ∫ z' in A, (κ z').real S ∂τ ≤ ∫ z' in A, (κ z).real S+δ ∂τ :=
      setIntegral_mono_on (integrable_kernel_real τ κ hS).integrableOn
        (integrable_const _).integrableOn (hQ (Q z)) (by
          intro z' hz'
          have := (abs_le.mp (hclose z' z hz')).2
          linarith)
    rw [integral_const] at H
    simp only [hAreal, smul_eq_mul] at H
    have := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hw.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using this
  change -δ ≤ (τ.real A)⁻¹ * _ - _ ∧ _ ≤ δ
  constructor <;> linarith

 

theorem kernel_entropy_finite_approx {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α] (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ Q : Z → (Fin k → Bool),
      (∀ i, MeasurableSet {z | Q z = i}) ∧
      ∀ᵐ z ∂τ, observationEntropy (kernelCell τ κ Q (Q z)) P ≤
        observationEntropy (κ z) P + ε := by
  let K : Set (α → ℝ) := Set.Icc 0 1
  have hK : IsCompact K := isCompact_Icc
  have hU := hK.uniformContinuousOn_of_continuous continuous_finiteShannon.continuousOn
  obtain ⟨δ,hδ,Hδ⟩ := Metric.uniformContinuousOn_iff.mp hU ε hε
  let p : Z → α → ℝ := fun z a => (κ z).real {y | P y = a}
  have hpK z : p z ∈ K := ⟨fun a => measureReal_nonneg, fun a => measureReal_le_one⟩
  obtain ⟨k,Q,hQ,HQ⟩ := finite_measurable_small_fibers p
    (measurable_pi_iff.mpr (fun a => measurable_kernel_real κ (hP a))) hK hpK
    (show 0 < δ/2 by positivity)
  refine ⟨k,Q,hQ,?_⟩
  filter_upwards [ae_nonnull_fiber τ Q] with z hz
  let q : α → ℝ := fun a => (kernelCell τ κ Q (Q z)).real {y | P y = a}
  have hqK : q ∈ K := ⟨fun a => measureReal_nonneg, fun a => measureReal_le_one⟩
  have hdist : dist q (p z) < δ := by
    apply lt_of_le_of_lt ((dist_pi_le_iff (show 0 ≤ δ/2 by positivity)).mpr ?_) (show δ/2 < δ by linarith)
    intro a
    rw [Real.dist_eq]
    exact kernelCell_real_close τ κ Q hQ (hP a) (fun z z' H =>
      (Real.dist_eq _ _ ▸ (dist_le_pi_dist (p z) (p z') a)).trans (HQ z z' H).le) z hz
  have H := Hδ q hqK (p z) (hpK z) hdist
  rw [Real.dist_eq] at H
  change finiteShannon q ≤ finiteShannon (p z) + ε
  have := (abs_lt.mp H).2
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma integrable_finite_values {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) [IsFiniteMeasure τ] (Q : Z → ι)
    (hQ : ∀ i, MeasurableSet {z | Q z = i}) (c : ι → ℝ) :
    Integrable (fun z => c (Q z)) τ := by
  have H : (fun z => c (Q z)) = fun z =>
      ∑ i, {z | Q z = i}.indicator (fun _ => c i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [H]
  exact integrable_finsetSum _ (fun i _ => (integrable_const (c i)).indicator (hQ i))

lemma integral_finite_values {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) [IsFiniteMeasure τ] (Q : Z → ι)
    (hQ : ∀ i, MeasurableSet {z | Q z = i}) (c : ι → ℝ) :
    (∫ z, c (Q z) ∂τ) = ∑ i, τ.real {z | Q z = i} * c i := by
  have H : (fun z => c (Q z)) = fun z =>
      ∑ i, {z | Q z = i}.indicator (fun _ => c i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [H,integral_finsetSum _ (fun i _ => (integrable_const (c i)).indicator (hQ i))]
  simp only [integral_indicator_const _ (hQ _), smul_eq_mul]

lemma observationEntropyRate_nonneg {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    0 ≤ observationEntropyRate μ T P := by
  unfold observationEntropyRate
  apply le_csInf
  · exact ⟨_,1,(show (1:ℕ) ≤ 1 from le_rfl),rfl⟩
  · rintro _ ⟨N,_,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _ (orbitName_measurable_fiber hT hP N))
      (Nat.cast_nonneg _)

lemma observationEntropyRate_le_block {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) {N : ℕ} (hN : 1 ≤ N) :
    observationEntropyRate μ T P ≤ observationEntropy μ (orbitName T P N)/(N:ℝ) := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro _ ⟨k,_,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _ (orbitName_measurable_fiber hT hP k))
      (Nat.cast_nonneg _)
  · exact ⟨N,hN,rfl⟩

 

theorem kernel_entropyRate_le_block {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α] (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z))
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) {N : ℕ} (hN : 1 ≤ N) :
    observationEntropyRate (κ ∘ₘ τ) T P * (N:ℝ) ≤
      ∫ z, observationEntropy (κ z) (orbitName T P N) ∂τ := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  let R := orbitName T P N
  have hR := orbitName_measurable_fiber hT hP N
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k,Q,hQ,HQ⟩ := kernel_entropy_finite_approx τ κ R hR hε
  let w := fun i => τ.real {z | Q z = i}
  let ν := kernelCell τ κ Q
  have hmix := kernel_finite_cells τ κ Q hQ
  have hrate := observationEntropyRate_finite_mixture (κ ∘ₘ τ) ν w
    (fun _ => measureReal_nonneg) (observation_distribution_sum τ Q hQ) hmix
    (kernel_mixture_preserving τ κ hT hκ) (fun i => kernelCell_preserving τ κ Q i hT hκ) P hP
  rw [hrate,Finset.sum_mul]
  have H : (∑ i, w i * observationEntropyRate (ν i) T P * (N:ℝ)) ≤
      ∑ i, w i * observationEntropy (ν i) R := by
    apply Finset.sum_le_sum
    intro i _
    have H := (le_div_iff₀ hNr).mp (observationEntropyRate_le_block (ν i) hT P hP hN)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H
      (show 0 ≤ w i from measureReal_nonneg)
  apply H.trans
  rw [← integral_finite_values τ Q hQ (fun i => observationEntropy (ν i) R)]
  have H' := integral_mono_ae (integrable_finite_values τ Q hQ (fun i => observationEntropy (ν i) R))
    ((integrable_kernel_entropy τ κ R hR).add (integrable_const ε)) HQ
  change (∫ z, observationEntropy (ν (Q z)) R ∂τ) ≤
    ∫ z, observationEntropy (κ z) R + ε ∂τ at H'
  simpa only [integral_add (integrable_kernel_entropy τ κ R hR) (integrable_const ε),
    integral_const, probReal_univ, one_smul] using H'

lemma normalized_orbit_entropy_le {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    observationEntropy μ (orbitName T P N)/(N:ℝ) ≤ Real.log (Fintype.card α) := by
  by_cases hN : N = 0
  · subst N
    simpa only [Nat.cast_zero, _root_.div_zero] using Real.log_natCast_nonneg (Fintype.card α)
  · have H := finiteShannon_le_log_card (fun a =>
        show 0 ≤ μ.real {y | orbitName T P N y = a} from measureReal_nonneg)
        (observation_distribution_sum μ _ (orbitName_measurable_fiber hT hP N))
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] at H
    exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hN)).mpr (by
      simpa only [observationEntropy, mul_comm] using H)

lemma observationEntropyRate_eq_zero_of_measureEntropy {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (hzero : measureEntropy μ T = 0) {k : ℕ} (P : Y → Fin k)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ T P = 0 := by
  have H : ENNReal.ofReal (observationEntropyRate μ T P) ≤ measureEntropy μ T :=
    le_iSup_of_le k (le_iSup_of_le P (le_iSup_of_le hP le_rfl))
  rw [hzero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at H
  exact le_antisymm H (observationEntropyRate_nonneg μ hT P hP)

 

theorem measureEntropy_kernel_zero {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Kernel Z Y) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z))
    (hzero : ∀ᵐ z ∂τ, measureEntropy (κ z) T = 0) :
    measureEntropy (κ ∘ₘ τ) T = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro k
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  rw [le_bot_iff]
  change ENNReal.ofReal (observationEntropyRate (κ ∘ₘ τ) T P) = 0
  rw [ENNReal.ofReal_eq_zero]
  let F : ℕ → Z → ℝ := fun N z => observationEntropy (κ z) (orbitName T P N)/(N:ℝ)
  have hlim : Tendsto (fun N => ∫ z, F N z ∂τ) atTop (𝓝 0) := by
    have H := tendsto_integral_of_dominated_convergence (fun _ : Z => Real.log k)
      (fun N => ((measurable_kernel_entropy κ _ (orbitName_measurable_fiber hT hP N)).div_const _).aestronglyMeasurable)
      (integrable_const _) (fun N => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
          (observationEntropy_nonneg (κ z) _ (orbitName_measurable_fiber hT hP N)) (Nat.cast_nonneg N))]
        simpa only [Fintype.card_fin] using normalized_orbit_entropy_le (κ z) hT P hP N)
      (f := fun _ : Z => (0:ℝ)) (by
        filter_upwards [hκ,hzero] with z hz hz0
        simpa only [observationEntropyRate_eq_zero_of_measureEntropy (κ z) hT hz0 P hP]
          using tendsto_observationEntropyRate (κ z) hz P hP)
    simpa only [integral_zero] using H
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have H := kernel_entropyRate_le_block τ κ hT hκ P hP hN
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  change observationEntropyRate (κ ∘ₘ τ) T P ≤ ∫ z, observationEntropy (κ z) (orbitName T P N)/(N:ℝ) ∂τ
  rw [integral_div]
  exact (le_div_iff₀ hNr).mpr H

end PrimeDegreePackets
end
end

end OAI
