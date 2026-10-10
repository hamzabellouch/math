import Mathlib
import OAI.NumberTheory.PrimePackets.IntrinsicLeaves

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
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
namespace PrimeDegreePackets

 
def realLeafPeriods (ν : Measure ℝ) : AddSubgroup ℝ where
  carrier := {a | ν.map (fun x => x+a) = ν}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ν.map (fun x => x+(a+b)) = ν
    have H : (fun x : ℝ => x+(a+b)) = (fun x => x+b) ∘ (fun x => x+a) := by
      ext x
      simp only [Function.comp_apply,add_assoc]
    rw [H,←Measure.map_map (by fun_prop) (by fun_prop),ha,hb]
  neg_mem' := by
    intro a ha
    change ν.map (fun x => x + -a) = ν
    have H := congrArg (fun ρ : Measure ℝ => ρ.map (fun x => x + -a)) ha
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at H
    simpa only [Function.comp_def,add_neg_cancel_right,Measure.map_id'] using H.symm

@[simp] lemma mem_realLeafPeriods (ν : Measure ℝ) (a : ℝ) :
    a ∈ realLeafPeriods ν ↔ ν.map (fun x => x+a) = ν := Iff.rfl

lemma continuous_integral_translate (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (f : C_c(ℝ,ℝ)) : Continuous (fun a : ℝ => ∫ x, f (x+a) ∂ν) := by
  have H := ((f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_const (μ := ν) (1:ℝ))
    (f.continuous.comp continuous_neg)).comp continuous_neg
  convert H using 1
  ext a
  simp only [Function.comp_apply,convolution_def,ContinuousLinearMap.mul_apply',one_mul]
  congr 1
  funext x
  congr 1
  simp

lemma realLeafPeriods_eq_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    (realLeafPeriods ν : Set ℝ) =
      ⋂ f : C_c(ℝ,ℝ), {a | (∫ x, f (x+a) ∂ν) = ∫ x, f x ∂ν} := by
  ext a
  simp only [mem_iInter,mem_ofPred_eq]
  constructor
  · intro ha f
    change ν.map (fun x => x+a) = ν at ha
    have H := integral_map (μ := ν) («φ» := fun x : ℝ => x+a)
      (f := fun x => f x) (by fun_prop) f.continuous.aestronglyMeasurable
    rw [ha] at H
    exact H.symm
  · intro ha
    have : (ν.map (fun x : ℝ => x+a)).Regular :=
      Measure.Regular.map (Homeomorph.addRight a)
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := ν) («φ» := fun x : ℝ => x+a)
      (f := fun x => f x) (by fun_prop) f.continuous.aestronglyMeasurable]
    exact ha f

 

theorem isClosed_realLeafPeriods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsClosed (realLeafPeriods ν : Set ℝ) := by
  rw [realLeafPeriods_eq_tests]
  exact isClosed_iInter fun f => isClosed_eq (continuous_integral_translate ν f) continuous_const

lemma realLeafPeriods_eq_top_of_dense (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hd : Dense (realLeafPeriods ν : Set ℝ)) : realLeafPeriods ν = ⊤ := by
  apply SetLike.coe_injective
  change (realLeafPeriods ν : Set ℝ) = univ
  rw [←(isClosed_realLeafPeriods ν).closure_eq,hd.closure_eq]

 

theorem realLeaf_invariant_of_small_periods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hs : ∀ ε > 0, ∃ a ∈ realLeafPeriods ν, a ∈ Set.Ioo 0 ε) (a : ℝ) :
    ν.map (fun x => x+a) = ν := by
  have H := realLeafPeriods_eq_top_of_dense ν ((realLeafPeriods ν).dense_of_not_isolated_zero hs)
  change a ∈ realLeafPeriods ν
  rw [H]
  trivial

 

theorem realLeafPeriods_top_or_cyclic (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    realLeafPeriods ν = ⊤ ∨ ∃ a : ℝ, realLeafPeriods ν = AddSubgroup.zmultiples a := by
  rcases (realLeafPeriods ν).dense_or_cyclic with hd | ⟨a,ha⟩
  · exact Or.inl (realLeafPeriods_eq_top_of_dense ν hd)
  · right
    exact ⟨a,by simpa only [AddSubgroup.zmultiples_eq_closure] using ha⟩

end PrimeDegreePackets


namespace PrimeDegreePackets

abbrev leafTestSpace (N : ℕ) :=
  {f : C(ℝ,ℝ) // ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0}

instance (N : ℕ) : SecondCountableTopology (leafTestSpace N) :=
  Subtype.secondCountableTopology
    (s := {f : C(ℝ,ℝ) | ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0})

instance (N : ℕ) : Nonempty (leafTestSpace N) := ⟨⟨0,fun _ _ => rfl⟩⟩

 
def leafTest (N k : ℕ) : C_c(ℝ,ℝ) :=
  ⟨(denseSeq (leafTestSpace N) k).val,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (by
        intro x hx
        by_contra h
        exact hx ((denseSeq (leafTestSpace N) k).prop x h)) isClosed_Icc)⟩

lemma leafTest_apply (N k : ℕ) (x : ℝ) :
    leafTest N k x = (denseSeq (leafTestSpace N) k).val x := rfl

lemma continuous_leafTestSpace_integral (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N : ℕ) (a : ℝ) : Continuous
      (fun f : leafTestSpace N => ∫ x, f.val (x+a) ∂ν) := by
  rw [←continuousOn_univ]
  apply continuousOn_integral_of_compact_support
    ((Homeomorph.addRight a).isCompact_preimage.mpr (isCompact_Icc (a := -(N:ℝ)) (b := N)))
  · have H : Continuous (fun p : leafTestSpace N × ℝ => p.1.val (p.2+a)) := by
      exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_snd.add_const a))
    exact H.continuousOn
  · intro f x _ hx
    exact f.prop (x+a) hx

 
lemma realLeafPeriods_iff_countable_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (a : ℝ) :
    a ∈ realLeafPeriods ν ↔ ∀ N k : ℕ,
      (∫ x, leafTest N k (x+a) ∂ν) = ∫ x, leafTest N k x ∂ν := by
  rw [show a ∈ realLeafPeriods ν ↔ ∀ f : C_c(ℝ,ℝ),
      (∫ x, f (x+a) ∂ν) = ∫ x, f x ∂ν from by
    rw [←SetLike.mem_coe,realLeafPeriods_eq_tests]
    simp only [mem_iInter,mem_ofPred_eq]]
  constructor
  · intro h N k
    exact h _
  · intro h f
    obtain ⟨R,hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
    obtain ⟨N,hN⟩ := exists_nat_gt R
    have hs : ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0 := by
      intro x hx
      by_contra hf
      have hb := hR (subset_closure hf)
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hb
      have hb' := abs_le.mp (hb.trans hN.le)
      exact hx hb'
    let f' : leafTestSpace N := ⟨f.toContinuousMap,hs⟩
    have hh : (fun g : leafTestSpace N => ∫ x, g.val (x+a) ∂ν) =
        (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ν) := by
      apply (denseRange_denseSeq (leafTestSpace N)).equalizer
        (continuous_leafTestSpace_integral ν N a) (continuous_leafTestSpace_integral ν N 0)
      funext k
      simpa only [Function.comp_apply,add_zero,leafTest_apply] using h N k
    have H := congrFun hh f'
    simpa only [f',add_zero,CompactlySupportedContinuousMap.coe_toContinuousMap] using H

 

lemma continuous_leafTest_discrepancy (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N k : ℕ) : Continuous (fun a : ℝ =>
      (∫ x, leafTest N k (x+a) ∂ν) - ∫ x, leafTest N k x ∂ν) :=
  (continuous_integral_translate ν (leafTest N k)).sub continuous_const

lemma measurable_leafTest_discrepancy {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) (N k : ℕ) (a : ℝ) : Measurable (fun z =>
      (∫ x, leafTest N k (x+a) ∂κ z) - ∫ x, leafTest N k x ∂κ z) := by
  exact (((leafTest N k).continuous.comp (continuous_id.add_const a)).stronglyMeasurable.integral_kernel).measurable.sub
    ((leafTest N k).continuous.stronglyMeasurable.integral_kernel).measurable

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma realLeafPeriods_smul (ν : Measure ℝ) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    realLeafPeriods (c • ν) = realLeafPeriods ν := by
  ext a
  simp only [mem_realLeafPeriods,Measure.map_smul c (μ := ν) (f := fun x : ℝ => x+a)
    (measurable_id.add_const a).aemeasurable]
  constructor
  · intro he
    have H := congrArg (fun ρ : Measure ℝ => c⁻¹ • ρ) he
    simpa only [smul_smul,ENNReal.inv_mul_cancel hc0 hcT,one_smul] using H
  · exact congrArg (fun ρ : Measure ℝ => c • ρ)

lemma realLeafPeriods_scaling (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) (a : ℝ) :
    c*a ∈ realLeafPeriods (ν.map (Homeomorph.mulLeft₀ c hc)) ↔ a ∈ realLeafPeriods ν := by
  have H : (ν.map (Homeomorph.mulLeft₀ c hc)).map (fun x => x+c*a) =
      (ν.map (fun x => x+a)).map (Homeomorph.mulLeft₀ c hc) := by
    rw [Measure.map_map (by fun_prop) (Homeomorph.mulLeft₀ c hc).measurable,
      Measure.map_map (Homeomorph.mulLeft₀ c hc).measurable (by fun_prop)]
    congr 1
    ext x
    change c*x+c*a = c*(x+a)
    ring
  simp only [mem_realLeafPeriods,H]
  exact (Homeomorph.mulLeft₀ c hc).measurableEmbedding.map_injective.eq_iff

lemma realLeafPeriods_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (a : ℝ) :
    c*a ∈ realLeafPeriods
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) ↔
        a ∈ realLeafPeriods ν := by
  have hm : ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 1) =
      ν (Metric.ball 0 (1/c)) := by
    rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,realScaling_preimage_ball c 1 hc]
  unfold anchorNormalize
  rw [realLeafPeriods_smul _ _ (by rw [hm]; exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (by rw [hm]; exact ENNReal.inv_ne_top.mpr (hp _ (by positivity)).ne')]
  exact realLeafPeriods_scaling ν c hc.ne' a

 
def hasSmallLeafPeriod (ν : Measure ℝ) (R : ℝ) : Prop :=
  ∃ a : ℝ, a ∈ realLeafPeriods ν ∧ 0 < a ∧ a ≤ R

lemma hasSmallLeafPeriod_mono (ν : Measure ℝ) {r R : ℝ} (hr : r ≤ R) :
    hasSmallLeafPeriod ν r → hasSmallLeafPeriod ν R := by
  rintro ⟨a,ha,hp,hs⟩
  exact ⟨a,ha,hp,hs.trans hr⟩

lemma hasSmallLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (R : ℝ) :
    hasSmallLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) R ↔
      hasSmallLeafPeriod ν (R/c) := by
  constructor
  · rintro ⟨a,ha,hap,haR⟩
    refine ⟨a/c,?_,div_pos hap hc,(div_le_div_iff_of_pos_right hc).mpr haR⟩
    apply (realLeafPeriods_normalized_scaling ν hp c hc (a/c)).mp
    simpa only [mul_div_cancel₀ _ hc.ne'] using ha
  · rintro ⟨a,ha,hap,haR⟩
    exact ⟨c*a,(realLeafPeriods_normalized_scaling ν hp c hc a).mpr ha,
      mul_pos hc hap,by simpa only [mul_comm] using (le_div_iff₀ hc).mp haR⟩

 

lemma exists_pos_leafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) :
    (∃ a ∈ realLeafPeriods
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)), 0 < a) ↔
    ∃ a ∈ realLeafPeriods ν, 0 < a := by
  constructor
  · rintro ⟨a,ha,hap⟩
    refine ⟨a/c,?_,div_pos hap hc⟩
    apply (realLeafPeriods_normalized_scaling ν hp c hc (a/c)).mp
    simpa only [mul_div_cancel₀ _ hc.ne'] using ha
  · rintro ⟨a,ha,hap⟩
    exact ⟨c*a,(realLeafPeriods_normalized_scaling ν hp c hc a).mpr ha,mul_pos hc hap⟩

end PrimeDegreePackets

open MeasureTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets

lemma exists_compact_zero_iff_dense_tests {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [SeparableSpace T] [Nonempty T]
    (F : ℕ → T → ℝ) (hF : ∀ n, Continuous (F n)) :
    (∃ t : T, ∀ n, F n t = 0) ↔
      ∀ k : ℕ, ∃ j : ℕ, ∀ i : Fin (k+1),
        |F i (denseSeq T j)| < 1/((k:ℝ)+1) := by
  constructor
  · rintro ⟨t,ht⟩ k
    let U := ⋂ i : Fin (k+1), {t : T | |F i t| < 1/((k:ℝ)+1)}
    have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
      isOpen_lt (hF i).abs continuous_const
    have htU : t ∈ U := by
      simp only [U,mem_iInter,mem_ofPred_eq,ht,abs_zero]
      intro _
      positivity
    obtain ⟨j,hj⟩ := (denseRange_denseSeq T).exists_mem_open hU ⟨t,htU⟩
    exact ⟨j,fun i => mem_iInter.mp hj i⟩
  · intro h
    let C (k : ℕ) := ⋂ i : Fin (k+1), {t : T | |F i t| ≤ 1/((k:ℝ)+1)}
    have hclosed (k : ℕ) : IsClosed (C k) := isClosed_iInter fun i =>
      isClosed_le (hF i).abs continuous_const
    have hnonempty (k : ℕ) : (C k).Nonempty := by
      obtain ⟨j,hj⟩ := h k
      exact ⟨denseSeq T j,mem_iInter.mpr fun i => (hj i).le⟩
    have hanti (k : ℕ) : C (k+1) ⊆ C k := by
      intro t ht
      apply mem_iInter.mpr
      intro i
      have H : |F i t| ≤ 1/(((k+1:ℕ):ℝ)+1) :=
        mem_iInter.mp ht ⟨i.val,by omega⟩
      exact H.trans (Nat.one_div_le_one_div (Nat.le_succ k))
    obtain ⟨t,ht⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      hanti hnonempty (hclosed 0).isCompact hclosed
    refine ⟨t,fun i => ?_⟩
    have H : ∀ᶠ k : ℕ in atTop, |F i t| ≤ 1/((k:ℝ)+1) := by
      filter_upwards [eventually_ge_atTop i] with k hk
      exact mem_iInter.mp (mem_iInter.mp ht k) ⟨i,by omega⟩
    have hz : |F i t| ≤ 0 := ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat H
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

 

theorem measurableSet_exists_compact_zero {α T : Type*} [MeasurableSpace α]
    [TopologicalSpace T] [CompactSpace T] [SeparableSpace T] [Nonempty T]
    (F : ℕ → α → T → ℝ)
    (hm : ∀ n t, Measurable (fun x => F n x t))
    (hc : ∀ n x, Continuous (F n x)) :
    MeasurableSet {x : α | ∃ t : T, ∀ n, F n x t = 0} := by
  simp_rw [exists_compact_zero_iff_dense_tests (fun n => F n _) (fun n => hc n _)]
  simp_rw [Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j =>
    by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i : Fin (k+1) =>
        measurableSet_lt (hm i (denseSeq T j)).abs measurable_const

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurableSet_exists_leafPeriod_Icc {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] (a b : ℝ) :
    MeasurableSet {x : α | ∃ t ∈ Icc a b, t ∈ realLeafPeriods (κ x)} := by
  by_cases hab : a ≤ b
  · let T := ↥(Icc a b)
    let : Nonempty T := ⟨⟨a,le_rfl,hab⟩⟩
    let : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
    let : SecondCountableTopology T := Subtype.secondCountableTopology _
    let F (n : ℕ) (x : α) (t : T) : ℝ :=
      (∫ y, leafTest n.unpair.1 n.unpair.2 (y+t.val) ∂κ x) -
        ∫ y, leafTest n.unpair.1 n.unpair.2 y ∂κ x
    have H := measurableSet_exists_compact_zero F
      (fun n t => measurable_leafTest_discrepancy κ _ _ t.val)
      (fun n x => (continuous_leafTest_discrepancy (κ x) _ _).comp continuous_subtype_val)
    convert H using 1
    ext x
    constructor
    · rintro ⟨t,ht,hp⟩
      exact ⟨⟨t,ht⟩,fun n => sub_eq_zero.mpr
        ((realLeafPeriods_iff_countable_tests (κ x) t).mp hp _ _)⟩
    · rintro ⟨t,ht⟩
      refine ⟨t.val,t.prop,(realLeafPeriods_iff_countable_tests (κ x) t.val).mpr ?_⟩
      intro N k
      have H := ht (Nat.pair N k)
      simpa only [F,Nat.unpair_pair,sub_eq_zero] using H
  · have he : {x : α | ∃ t ∈ Icc a b, t ∈ realLeafPeriods (κ x)} = ∅ := by
      ext x
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,not_exists]
      rintro t ⟨ht,_⟩
      exact hab (ht.1.trans ht.2)
    rw [he]
    exact MeasurableSet.empty

 

theorem measurableSet_hasSmallLeafPeriod {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] (R : ℝ) :
    MeasurableSet {x : α | hasSmallLeafPeriod (κ x) R} := by
  have he : {x : α | hasSmallLeafPeriod (κ x) R} =
      ⋃ m : ℕ, {x : α | ∃ t ∈ Icc (1/((m:ℝ)+1)) R, t ∈ realLeafPeriods (κ x)} := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨t,ht,hp,hs⟩
      obtain ⟨m,hm⟩ := exists_nat_one_div_lt hp
      exact ⟨m,t,⟨hm.le,hs⟩,ht⟩
    · rintro ⟨m,t,ht,hp⟩
      exact ⟨t,hp,lt_of_lt_of_le (by positivity) ht.1,ht.2⟩
  rw [he]
  exact MeasurableSet.iUnion fun m => measurableSet_exists_leafPeriod_Icc κ _ _

 
theorem measurableSet_exists_pos_leafPeriod {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] :
    MeasurableSet {x : α | ∃ a ∈ realLeafPeriods (κ x), 0 < a} := by
  have he : {x : α | ∃ a ∈ realLeafPeriods (κ x), 0 < a} =
      ⋃ m : ℕ, {x : α | hasSmallLeafPeriod (κ x) ((m:ℝ)+1)} := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨a,ha,hap⟩
      obtain ⟨m,hm⟩ := exists_nat_gt a
      exact ⟨m,a,ha,hap,by linarith⟩
    · rintro ⟨m,a,ha,hap,_⟩
      exact ⟨a,ha,hap⟩
  rw [he]
  exact MeasurableSet.iUnion fun m => measurableSet_hasSmallLeafPeriod κ _

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_hasSmallLeafPeriod_scaling {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    {T : α → α} (hT : MeasurePreserving T μ μ) (c : ℝ) (hc : 1 ≤ c)
    (hcov : ∀ᵐ x ∂μ, κ (T x) =
      anchorNormalize ((κ x).map (Homeomorph.mulLeft₀ c (by linarith))) (Metric.ball 0 1))
    (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ x ∂μ, hasSmallLeafPeriod (κ x) R ↔ hasSmallLeafPeriod (κ x) (R/c) := by
  classical
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let E : Set α := {x | hasSmallLeafPeriod (κ x) R}
  let f : α → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_hasSmallLeafPeriod κ R)
  have he : ∀ᵐ x ∂μ, T x ∈ E ↔ hasSmallLeafPeriod (κ x) (R/c) := by
    filter_upwards [hp,hcov] with x hx hcovx
    change hasSmallLeafPeriod (κ (T x)) R ↔ _
    rw [hcovx]
    exact hasSmallLeafPeriod_normalized_scaling (κ x) hx c hc0 R
  have hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x := by
    filter_upwards [he] with x hx
    by_cases h : T x ∈ E
    · have hxE : x ∈ E := hasSmallLeafPeriod_mono (κ x)
        (div_le_self hR hc) (hx.mp h)
      simp only [f,indicator_of_mem h,indicator_of_mem hxE,le_refl]
    · simp only [f,indicator_of_notMem h]
      exact bot_le
  have heq := ae_eq_of_measurePreserving_ennreal_ge μ hT hf.aemeasurable
    (Eventually.of_forall fun x => show f x ≤ 1 from by
      by_cases hx : x ∈ E <;> simp [f,hx]) hmono
  filter_upwards [he,heq] with x hx heqx
  have hiff : x ∈ E ↔ T x ∈ E := by
    by_cases hxE : x ∈ E <;> by_cases hTE : T x ∈ E <;>
      simp_all [f,Function.comp_apply]
  exact hiff.trans hx

 

theorem ae_realLeafPeriods_bot_or_top {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, realLeafPeriods (κ x) = ⊥ ∨ realLeafPeriods (κ x) = ⊤ := by
  have H (m k : ℕ) : ∀ᵐ x ∂μ, hasSmallLeafPeriod (κ x) ((m:ℝ)+1) ↔
      hasSmallLeafPeriod (κ x) (1/((k:ℝ)+1)) := by
    let c : ℝ := ((m:ℝ)+1)*((k:ℝ)+1)
    have hc : 1 ≤ c := by
      dsimp [c]
      nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨T,hT,hcov⟩ := hscaling c (zero_lt_one.trans_le hc)
    have he := ae_hasSmallLeafPeriod_scaling μ κ hp hT c hc hcov ((m:ℝ)+1) (by positivity)
    have hdiv : ((m:ℝ)+1)/c = 1/((k:ℝ)+1) := by
      dsimp [c]
      field_simp
    simpa only [hdiv] using he
  have HH : ∀ᵐ x ∂μ, ∀ m k : ℕ, hasSmallLeafPeriod (κ x) ((m:ℝ)+1) ↔
      hasSmallLeafPeriod (κ x) (1/((k:ℝ)+1)) := by
    exact ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => H m k
  filter_upwards [HH] with x hx
  by_cases hn : ∃ a ∈ realLeafPeriods (κ x), 0 < a
  · right
    obtain ⟨a,ha,hap⟩ := hn
    obtain ⟨m,hm⟩ := exists_nat_gt a
    have hlarge : hasSmallLeafPeriod (κ x) ((m:ℝ)+1) :=
      ⟨a,ha,hap,by linarith⟩
    apply SetLike.coe_injective
    ext a
    simp only [AddSubgroup.coe_top,mem_univ,iff_true]
    apply realLeaf_invariant_of_small_periods
    intro ε hε
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨t,ht,htp,htr⟩ := (hx m k).mp hlarge
    exact ⟨t,ht,htp,htr.trans_lt hk⟩
  · left
    ext a
    rw [AddSubgroup.mem_bot]
    constructor
    · intro ha
      have ha0 : a ≤ 0 := le_of_not_gt fun h => hn ⟨a,ha,h⟩
      have hna : -a ≤ 0 := le_of_not_gt fun h => hn ⟨-a,(realLeafPeriods (κ x)).neg_mem ha,h⟩
      linarith
    · rintro rfl
      exact (realLeafPeriods (κ x)).zero_mem

end PrimeDegreePackets
end
end

end OAI
