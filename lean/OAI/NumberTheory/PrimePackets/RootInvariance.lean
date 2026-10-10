import Mathlib
import OAI.NumberTheory.PrimePackets.LeafPeriods
import OAI.NumberTheory.PrimePackets.ScalingCovariance

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
open MeasureTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_periods_bot_or_top (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊥ ∨
      realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊤ := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x := ae_intrinsicRootKernel_eq hij μ hfree
  have hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    filter_upwards [heq,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hp
    rwa [hx]
  have H := ae_realLeafPeriods_bot_or_top μ κ hp (by
    intro c hc
    let T : X (d+1) → X (d+1) := fun x => rightAction x (rootCanonicalFlow d j (Real.log c))
    have hT : MeasurePreserving T μ μ := rootCanonicalFlow_preserving d j (Real.log c) μ hA
    refine ⟨T,hT,?_⟩
    have heqmap : ∀ᵐ x ∂μ.map T, κ x = intrinsicRootLeaf hij μ x := by
      rw [hT.map_eq]
      exact heq
    have heqT : ∀ᵐ x ∂μ, κ (T x) = intrinsicRootLeaf hij μ (T x) :=
      ae_of_ae_map hT.measurable.aemeasurable heqmap
    filter_upwards [heq,heqT,ae_intrinsicRootLeaf_canonical d hij μ hA (Real.log c)] with x hx hTx hcq
    rw [hTx,hx]
    simpa only [Real.exp_log hc,T] using hcq)
  filter_upwards [heq,H] with x hx h
  rwa [hx] at h

 

theorem root_invariant_of_nonzero_intrinsic_period (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hp : ∀ᵐ x ∂μ, ∃ v : ℝ, v ≠ 0 ∧ v ∈ realLeafPeriods (intrinsicRootLeaf hij μ x))
    (a : ℝ) : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  apply root_invariant_of_intrinsic d hij μ hA
  filter_upwards [hp,ae_intrinsicRootLeaf_periods_bot_or_top d hij μ hA] with x hx hperiod
  obtain ⟨v,hv,hvp⟩ := hx
  rcases hperiod with hb | ht
  · rw [hb,AddSubgroup.mem_bot] at hvp
    exact (hv hvp).elim
  · intro t
    change t ∈ realLeafPeriods (intrinsicRootLeaf hij μ x)
    rw [ht]
    trivial

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_intrinsicRootLeaf_exists_period_diagonal (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (u : LogCoordinates d) :
    ∀ᵐ x ∂μ, (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a) ↔
      ∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u))), 0 < a := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let ell : Fin (d+1) → ℝ := Fin.snoc u (-∑ k, u k)
  have hell : ∑ k, ell k = 0 := by simp [ell,Fin.sum_univ_castSucc]
  have ha : diagonalOneParameter ell hell 1 = diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext k
    simp [ell]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell 1 μ hfree (by rw [ha]; exact hA u)
  have hs : rootTimeScaling ell i j 1 =
      Homeomorph.mulLeft₀ (Real.exp (ell j-ell i)) (Real.exp_ne_zero _) := by
    apply Homeomorph.ext
    intro t
    simp [rootTimeScaling]
  rw [ha,hs] at H
  filter_upwards [H,ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hspec hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hspec.1
  rw [hx]
  exact (exists_pos_leafPeriod_normalized_scaling _ hp _ (Real.exp_pos _)).symm

 

theorem intrinsicRootLeaf_periods_ergodic_alternative (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    (∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) ∨
      (∀ᵐ x ∂μ, realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊥) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  let S : Set (X (d+1)) := {x | ∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a}
  have hm : NullMeasurableSet S μ := by
    apply (measurableSet_exists_pos_leafPeriod κ).nullMeasurableSet.congr
    filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree] with x hx
    change (∃ a ∈ realLeafPeriods (κ x), 0 < a) =
      (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a)
    rw [show κ x = intrinsicRootLeaf hij μ x from hx]
  have he : EventuallyEmptyOrUniv S (ae μ) :=
    aeconst_of_forall_preimage_smul_ae_eq (Multiplicative (LogCoordinates d)) hm (by
      intro u
      filter_upwards [ae_intrinsicRootLeaf_exists_period_diagonal d hij μ hA u.toAdd] with x hx
      change (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u.toAdd))), 0 < a) =
        (∃ a ∈ realLeafPeriods (intrinsicRootLeaf hij μ x), 0 < a)
      exact propext hx.symm)
  rcases eventuallyEmptyOrUniv_iff.mp he with hp | hn
  · left
    apply root_invariant_of_nonzero_intrinsic_period d hij μ hA
    filter_upwards [hp] with x hx
    obtain ⟨a,ha,hap⟩ := hx
    exact ⟨a,hap.ne',ha⟩
  · right
    filter_upwards [hn,ae_intrinsicRootLeaf_periods_bot_or_top d hij μ hA] with x hx hp
    rcases hp with hb | ht
    · exact hb
    · exact (hx ⟨1,by rw [ht]; trivial,zero_lt_one⟩).elim

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma realMeasures_eq_iff_leafTests (ν ρ : Measure ℝ)
    [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ] :
    ν = ρ ↔ ∀ N k : ℕ, (∫ x, leafTest N k x ∂ν) = ∫ x, leafTest N k x ∂ρ := by
  constructor
  · rintro rfl N k
    rfl
  · intro h
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    obtain ⟨R,hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
    obtain ⟨N,hN⟩ := exists_nat_gt R
    have hs : ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0 := by
      intro x hx
      by_contra hf
      have hb := hR (subset_closure hf)
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hb
      exact hx (abs_le.mp (hb.trans hN.le))
    let f' : leafTestSpace N := ⟨f.toContinuousMap,hs⟩
    have hh : (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ν) =
        (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ρ) := by
      apply (denseRange_denseSeq (leafTestSpace N)).equalizer
        (continuous_leafTestSpace_integral ν N 0) (continuous_leafTestSpace_integral ρ N 0)
      funext k
      simpa only [Function.comp_apply,add_zero,leafTest_apply] using h N k
    have H := congrFun hh f'
    simpa only [f',add_zero,CompactlySupportedContinuousMap.coe_toContinuousMap] using H

 
def projectiveLeafPeriod (ν : Measure ℝ) (p : ℝ × ℝ) : Prop :=
  ν.map (fun x => x+p.1) = ENNReal.ofReal (Real.exp p.2) • ν

lemma projectiveLeafPeriod_iff_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (p : ℝ × ℝ) :
    projectiveLeafPeriod ν p ↔ ∀ N k : ℕ,
      (∫ x, leafTest N k (x+p.1) ∂ν) = Real.exp p.2 * ∫ x, leafTest N k x ∂ν := by
  let : (ν.map (fun x : ℝ => x+p.1)).Regular := Measure.Regular.map (Homeomorph.addRight p.1)
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal (Real.exp p.2) • ν) :=
    IsFiniteMeasureOnCompacts.smul ν ENNReal.ofReal_ne_top
  unfold projectiveLeafPeriod
  rw [realMeasures_eq_iff_leafTests]
  congr! 2
  rename_i N k
  rw [integral_map (μ := ν) («φ» := fun x : ℝ => x+p.1)
    (f := fun x => leafTest N k x) (by fun_prop)
    (leafTest N k).continuous.aestronglyMeasurable,
    integral_smul_measure,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

lemma continuous_projectiveLeaf_discrepancy (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N k : ℕ) : Continuous (fun p : ℝ × ℝ =>
      (∫ x, leafTest N k (x+p.1) ∂ν) - Real.exp p.2 * ∫ x, leafTest N k x ∂ν) :=
  ((continuous_integral_translate ν (leafTest N k)).comp continuous_fst).sub
    ((Real.continuous_exp.comp continuous_snd).mul continuous_const)

lemma measurable_projectiveLeaf_discrepancy {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) (N k : ℕ) (p : ℝ × ℝ) : Measurable (fun z =>
      (∫ x, leafTest N k (x+p.1) ∂κ z) - Real.exp p.2 * ∫ x, leafTest N k x ∂κ z) := by
  exact (((leafTest N k).continuous.comp (continuous_id.add_const p.1)).stronglyMeasurable.integral_kernel).measurable.sub
    (measurable_const.mul ((leafTest N k).continuous.stronglyMeasurable.integral_kernel).measurable)

lemma isClosed_projectiveLeafPeriods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsClosed {p | projectiveLeafPeriod ν p} := by
  have he : {p | projectiveLeafPeriod ν p} =
      ⋂ N : ℕ, ⋂ k : ℕ, {p : ℝ × ℝ |
        (∫ x, leafTest N k (x+p.1) ∂ν) - Real.exp p.2 * ∫ x, leafTest N k x ∂ν = 0} := by
    ext p
    simp only [Set.mem_ofPred_eq,mem_iInter,sub_eq_zero,projectiveLeafPeriod_iff_tests]
  rw [he]
  exact isClosed_iInter fun N => isClosed_iInter fun k =>
    isClosed_eq (continuous_projectiveLeaf_discrepancy ν N k) continuous_const

 

lemma projectiveLeafPeriod_zero_time (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : 0 < ν (Metric.ball 0 1)) (b : ℝ) (h : projectiveLeafPeriod ν (0,b)) : b = 0 := by
  have he : ν = ENNReal.ofReal (Real.exp b) • ν := by
    simpa [projectiveLeafPeriod] using h
  have H := congrArg (fun ρ : Measure ℝ => ρ (Metric.ball 0 1)) he
  rw [Measure.smul_apply,smul_eq_mul] at H
  have HH : (1:ℝ≥0∞) = ENNReal.ofReal (Real.exp b) :=
    (ENNReal.mul_left_inj hp.ne' measure_ball_lt_top.ne).mp (by simpa only [one_mul] using H)
  exact (Real.exp_eq_one_iff b).mp (ENNReal.ofReal_eq_one.mp HH.symm)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma projectiveLeafPeriod_smul (ν : Measure ℝ) (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqT : q ≠ ∞)
    (p : ℝ × ℝ) : projectiveLeafPeriod (q • ν) p ↔ projectiveLeafPeriod ν p := by
  unfold projectiveLeafPeriod
  rw [Measure.map_smul _ (f := fun value : ℝ => value+p.1) (by fun_prop),
    smul_comm (ENNReal.ofReal (Real.exp p.2)) q ν]
  constructor
  · intro he
    have H := congrArg (fun ρ : Measure ℝ => q⁻¹ • ρ) he
    simpa only [smul_smul,←mul_assoc,ENNReal.inv_mul_cancel hq0 hqT,one_mul,one_smul] using H
  · exact congrArg (fun ρ : Measure ℝ => q • ρ)

lemma projectiveLeafPeriod_scaling (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) (p : ℝ × ℝ) :
    projectiveLeafPeriod (ν.map (Homeomorph.mulLeft₀ c hc)) (c*p.1,p.2) ↔
      projectiveLeafPeriod ν p := by
  have H : (ν.map (Homeomorph.mulLeft₀ c hc)).map (fun x => x+c*p.1) =
      (ν.map (fun x => x+p.1)).map (Homeomorph.mulLeft₀ c hc) := by
    rw [Measure.map_map (by fun_prop) (Homeomorph.mulLeft₀ c hc).measurable,
      Measure.map_map (Homeomorph.mulLeft₀ c hc).measurable (by fun_prop)]
    congr 1
    ext x
    change c*x+c*p.1 = c*(x+p.1)
    ring
  unfold projectiveLeafPeriod
  rw [H,←Measure.map_smul _ (Homeomorph.mulLeft₀ c hc).measurable.aemeasurable]
  exact (Homeomorph.mulLeft₀ c hc).measurableEmbedding.map_injective.eq_iff

lemma projectiveLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ) :
    projectiveLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) (c*p.1,p.2) ↔
        projectiveLeafPeriod ν p := by
  have hm : ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 1) =
      ν (Metric.ball 0 (1/c)) := by
    rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,realScaling_preimage_ball c 1 hc]
  unfold anchorNormalize
  rw [projectiveLeafPeriod_smul _ _ (by rw [hm]; exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (by rw [hm]; exact ENNReal.inv_ne_top.mpr (hp _ (by positivity)).ne')]
  exact projectiveLeafPeriod_scaling ν c hc.ne' p

 

def boundedProjectiveLeafPeriod (ν : Measure ℝ) (R l u : ℝ) : Prop :=
  ∃ p : ℝ × ℝ, projectiveLeafPeriod ν p ∧ |p.1| ≤ R ∧ p.2 ∈ Icc l u

lemma boundedProjectiveLeafPeriod_mono (ν : Measure ℝ) {r R l u : ℝ} (hr : r ≤ R) :
    boundedProjectiveLeafPeriod ν r l u → boundedProjectiveLeafPeriod ν R l u := by
  rintro ⟨p,hp,hrp,hs⟩
  exact ⟨p,hp,hrp.trans hr,hs⟩

lemma boundedProjectiveLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (R l u : ℝ) :
    boundedProjectiveLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) R l u ↔
      boundedProjectiveLeafPeriod ν (R/c) l u := by
  constructor
  · rintro ⟨p,hp',hpa,hpb⟩
    refine ⟨(p.1/c,p.2),?_,?_,hpb⟩
    · apply (projectiveLeafPeriod_normalized_scaling ν hp c hc (p.1/c,p.2)).mp
      simpa only [mul_div_cancel₀ _ hc.ne'] using hp'
    · change |p.1/c| ≤ R/c
      rw [abs_div,abs_of_pos hc]
      exact (div_le_div_iff_of_pos_right hc).mpr hpa
  · rintro ⟨p,hp',hpa,hpb⟩
    refine ⟨(c*p.1,p.2),(projectiveLeafPeriod_normalized_scaling ν hp c hc p).mpr hp',?_,hpb⟩
    change |c*p.1| ≤ R
    rw [abs_mul,abs_of_pos hc,mul_comm]
    exact (le_div_iff₀ hc).mp hpa

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurableSet_exists_projectiveLeafPeriod_mem {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)]
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    MeasurableSet {x : α | ∃ p ∈ K, projectiveLeafPeriod (κ x) p} := by
  by_cases he : K.Nonempty
  · let T := ↥K
    let : Nonempty T := he.to_subtype
    let : CompactSpace T := isCompact_iff_compactSpace.mp hK
    let : SecondCountableTopology T := Subtype.secondCountableTopology _
    let F (n : ℕ) (x : α) (p : T) : ℝ :=
      (∫ y, leafTest n.unpair.1 n.unpair.2 (y+p.val.1) ∂κ x) -
        Real.exp p.val.2 * ∫ y, leafTest n.unpair.1 n.unpair.2 y ∂κ x
    have H := measurableSet_exists_compact_zero F
      (fun n p => measurable_projectiveLeaf_discrepancy κ _ _ p.val)
      (fun n x => (continuous_projectiveLeaf_discrepancy (κ x) _ _).comp continuous_subtype_val)
    convert H using 1
    ext x
    constructor
    · rintro ⟨p,hp,hper⟩
      exact ⟨⟨p,hp⟩,fun n => sub_eq_zero.mpr
        ((projectiveLeafPeriod_iff_tests (κ x) p).mp hper _ _)⟩
    · rintro ⟨p,hp⟩
      refine ⟨p.val,p.prop,(projectiveLeafPeriod_iff_tests (κ x) p.val).mpr ?_⟩
      intro N k
      have H := hp (Nat.pair N k)
      simpa only [F,Nat.unpair_pair,sub_eq_zero] using H
  · simp only [Set.not_nonempty_iff_eq_empty.mp he,mem_empty_iff_false,false_and,exists_false,
      Set.ofPred_false,MeasurableSet.empty]

lemma measurableSet_boundedProjectiveLeafPeriod {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] (R l u : ℝ) :
    MeasurableSet {x : α | boundedProjectiveLeafPeriod (κ x) R l u} := by
  have he : {x : α | boundedProjectiveLeafPeriod (κ x) R l u} =
      {x : α | ∃ p ∈ (Icc (-R) R ×ˢ Icc l u), projectiveLeafPeriod (κ x) p} := by
    ext x
    simp only [Set.mem_ofPred_eq,boundedProjectiveLeafPeriod,mem_prod]
    constructor
    · rintro ⟨p,hp,ha,hb⟩
      exact ⟨p,⟨abs_le.mp ha,hb⟩,hp⟩
    · rintro ⟨p,⟨ha,hb⟩,hp⟩
      exact ⟨p,hp,abs_le.mpr ha,hb⟩
  rw [he]
  exact measurableSet_exists_projectiveLeafPeriod_mem κ _ (isCompact_Icc.prod isCompact_Icc)

 

lemma not_forall_boundedProjectiveLeafPeriod (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : 0 < ν (Metric.ball 0 1)) (l u : ℝ) (hzero : (0:ℝ) ∉ Icc l u) :
    ¬ ∀ k : ℕ, boundedProjectiveLeafPeriod ν (1/((k:ℝ)+1)) l u := by
  intro H
  let C (k : ℕ) : Set (ℝ × ℝ) := {p | projectiveLeafPeriod ν p} ∩
    (Icc (-(1/((k:ℝ)+1))) (1/((k:ℝ)+1)) ×ˢ Icc l u)
  have hc (k : ℕ) : IsClosed (C k) :=
    (isClosed_projectiveLeafPeriods ν).inter (isClosed_Icc.prod isClosed_Icc)
  have hne (k : ℕ) : (C k).Nonempty := by
    obtain ⟨p,hp,ha,hb⟩ := H k
    exact ⟨p,hp,abs_le.mp ha,hb⟩
  have ha (k : ℕ) : C (k+1) ⊆ C k := by
    rintro p ⟨hp,ha,hb⟩
    refine ⟨hp,?_,hb⟩
    exact abs_le.mp ((abs_le.mpr ha).trans (Nat.one_div_le_one_div (Nat.le_succ k)))
  have hcomp : IsCompact (C 0) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (hc 0) (fun _ h => h.2)
  obtain ⟨p,hpC⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C ha hne hcomp hc
  have hpa : ∀ᶠ k : ℕ in atTop, |p.1| ≤ 1/((k:ℝ)+1) :=
    Eventually.of_forall fun k => abs_le.mpr (mem_iInter.mp hpC k).2.1
  have hp0 : p.1 = 0 := abs_eq_zero.mp (le_antisymm
    (ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat hpa) (abs_nonneg _))
  have hper := (mem_iInter.mp hpC 0).1
  have hrect := (mem_iInter.mp hpC 0).2.2
  have he : p = (0,p.2) := Prod.ext hp0 rfl
  rw [he] at hper
  have hp2 : p.2 = 0 := projectiveLeafPeriod_zero_time ν hp p.2 hper
  exact hzero (hp2 ▸ hrect)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_boundedProjectiveLeafPeriod_scaling {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    {T : α → α} (hT : MeasurePreserving T μ μ) (c : ℝ) (hc : 1 ≤ c)
    (hcov : ∀ᵐ x ∂μ, κ (T x) =
      anchorNormalize ((κ x).map (Homeomorph.mulLeft₀ c (by linarith))) (Metric.ball 0 1))
    (R l u : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ x ∂μ, boundedProjectiveLeafPeriod (κ x) R l u ↔
      boundedProjectiveLeafPeriod (κ x) (R/c) l u := by
  classical
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let E : Set α := {x | boundedProjectiveLeafPeriod (κ x) R l u}
  let f : α → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_boundedProjectiveLeafPeriod κ R l u)
  have he : ∀ᵐ x ∂μ, T x ∈ E ↔ boundedProjectiveLeafPeriod (κ x) (R/c) l u := by
    filter_upwards [hp,hcov] with x hx hcovx
    change boundedProjectiveLeafPeriod (κ (T x)) R l u ↔ _
    rw [hcovx]
    exact boundedProjectiveLeafPeriod_normalized_scaling (κ x) hx c hc0 R l u
  have hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x := by
    filter_upwards [he] with x hx
    by_cases h : T x ∈ E
    · have hxE : x ∈ E := boundedProjectiveLeafPeriod_mono (κ x)
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

lemma ae_projectiveLeafPeriod_avoids_interval {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1))
    (l u : ℝ) (hzero : (0:ℝ) ∉ Icc l u) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (κ x) p → p.2 ∉ Icc l u := by
  have H (m k : ℕ) : ∀ᵐ x ∂μ, boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u ↔
      boundedProjectiveLeafPeriod (κ x) (1/((k:ℝ)+1)) l u := by
    let c : ℝ := ((m:ℝ)+1)*((k:ℝ)+1)
    have hc : 1 ≤ c := by
      dsimp [c]
      nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨T,hT,hcov⟩ := hscaling c (zero_lt_one.trans_le hc)
    have he := ae_boundedProjectiveLeafPeriod_scaling μ κ hp hT c hc hcov ((m:ℝ)+1) l u (by positivity)
    have hdiv : ((m:ℝ)+1)/c = 1/((k:ℝ)+1) := by
      dsimp [c]
      field_simp
    simpa only [hdiv] using he
  have HH : ∀ᵐ x ∂μ, ∀ m k : ℕ, boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u ↔
      boundedProjectiveLeafPeriod (κ x) (1/((k:ℝ)+1)) l u :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => H m k
  filter_upwards [hp,HH] with x hx hxx
  intro p hper hmem
  obtain ⟨m,hm⟩ := exists_nat_gt |p.1|
  have hlarge : boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u := ⟨p,hper,by linarith,hmem⟩
  exact not_forall_boundedProjectiveLeafPeriod (κ x) (hx 1 zero_lt_one) l u hzero
    (fun k => (hxx m k).mp hlarge)

lemma exists_nat_mem_Icc_inv_succ {b : ℝ} (hb : 0 < b) :
    ∃ n : ℕ, b ∈ Icc (1/((n:ℝ)+1)) ((n:ℝ)+1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt b
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hb
  refine ⟨max m k,?_,?_⟩
  · exact (Nat.one_div_le_one_div (Nat.le_max_right m k)).trans hk.le
  · have H : (m:ℝ) ≤ ((max m k:ℕ):ℝ) := Nat.cast_le.mpr (Nat.le_max_left m k)
    linarith

 

theorem ae_projectiveLeafPeriod_multiplier_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (κ x) p → p.2 = 0 := by
  have Hpos (n : ℕ) := ae_projectiveLeafPeriod_avoids_interval μ κ hp hscaling
    (1/((n:ℝ)+1)) ((n:ℝ)+1) (by
      intro h
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith [h.1])
  have Hneg (n : ℕ) := ae_projectiveLeafPeriod_avoids_interval μ κ hp hscaling
    (-((n:ℝ)+1)) (-(1/((n:ℝ)+1))) (by
      intro h
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith [h.2])
  filter_upwards [ae_all_iff.mpr Hpos,ae_all_iff.mpr Hneg] with x hx hy
  intro p hp
  rcases lt_trichotomy (0:ℝ) p.2 with h | h | h
  · obtain ⟨n,hn⟩ := exists_nat_mem_Icc_inv_succ h
    exact (hx n p hp hn).elim
  · exact h.symm
  · obtain ⟨n,hn⟩ := exists_nat_mem_Icc_inv_succ (neg_pos.mpr h)
    exact (hy n p hp ⟨by linarith [hn.2],by linarith [hn.1]⟩).elim

end PrimeDegreePackets
end
end

end OAI
