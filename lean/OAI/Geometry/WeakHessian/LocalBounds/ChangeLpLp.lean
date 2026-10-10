import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergySlope
import OAI.Geometry.WeakHessian.Sobolev.NormMinimalRelaxedGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma changeLp_toLp {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Lp.LpToLpOfMeasureLeSMul hc hν (hf.toLp f) =
      (hf.of_measure_le_smul hc hν).toLp f := by
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hν (hf.toLp f)).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.coeFn_toLp).trans
      (hf.of_measure_le_smul hc hν).coeFn_toLp.symm)

omit [MetricSpace X] [BorelSpace X] in
lemma tendsto_toLp_changeMeasure {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {fs : ℕ → X → ℝ} {f : X → ℝ} (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m)
    (h : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ((hfs n).of_measure_le_smul hc hν).toLp (fs n))
      atTop (𝓝 ((hf.of_measure_le_smul hc hν).toLp f)) := by
  have H := (Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hc hν).continuous.tendsto _ |>.comp h
  simpa only [Function.comp_def, changeLp_toLp] using H

omit [BorelSpace X] in
lemma FiniteOnBoundedSets.of_measure_le_smul (hm : FiniteOnBoundedSets m)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m) : FiniteOnBoundedSets ν := by
  intro B hB
  exact lt_of_le_of_lt (hν B) (by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hm B hB))

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma changeLp_inverse {c d : ℝ≥0∞} (hc : c ≠ ∞) (hd : d ≠ ∞)
    (hν : ν ≤ c • m) (hm : m ≤ d • ν) (u : Lp ℝ 2 m) :
    Lp.LpToLpOfMeasureLeSMul hd hm (Lp.LpToLpOfMeasureLeSMul hc hν u) = u := by
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hd hm _).trans
    ((Measure.absolutelyContinuous_of_le_smul hm).ae_eq
      (Lp.coeFn_LpToLpOfMeasureLeSMul hc hν u))

omit [BorelSpace X] in
lemma relaxedGraph_changeMeasure {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {f D : Lp ℝ 2 m} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (Lp.LpToLpOfMeasureLeSMul hc hν f,Lp.LpToLpOfMeasureLeSMul hc hν D)
      ∈ l2RelaxedGraph ν := by
  let T := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hc hν
  let P : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) → WithLp 2 (Lp ℝ 2 ν × Lp ℝ 2 ν) :=
    fun p => WithLp.toLp 2 (T p.fst,T p.snd)
  have hP : Continuous P :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν) (Lp ℝ 2 ν)).symm.continuous.comp
      ((T.continuous.comp (WithLp.continuous_fst 2 _ _)).prodMk
        (T.continuous.comp (WithLp.continuous_snd 2 _ _)))
  have hraw : l2SlopeGraph m ⊆ P ⁻¹' l2RelaxedGraph ν := by
    intro p hp
    obtain ⟨u,hu,hum,hpf,hbound⟩ := hp
    apply subset_closure
    refine ⟨u,hu,hum.of_measure_le_smul hc hν,?_,?_⟩
    · change _ = T p.fst
      rw [← hpf]
      exact (changeLp_toLp hc hν hum).symm
    · change ∀ᵐ x ∂ν, (localSlope u x).toReal ≤ (T p.snd) x
      filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le hbound,
        Lp.coeFn_LpToLpOfMeasureLeSMul hc hν p.snd] with x hx hy
      rwa [hy]
  exact closure_minimal hraw (isClosed_l2RelaxedGraph.preimage hP) hD

lemma relaxedGradient_minimal_comparable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    (hfinite : FiniteOnBoundedSets m) {c d : ℝ≥0∞} (hc : c ≠ ∞) (hd : d ≠ ∞)
    (hν : ν ≤ c • m) (hm : m ≤ d • ν)
    {f D : Lp ℝ 2 m} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m)
    (hmin : ∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖) :
    ∀ E : Lp ℝ 2 ν,
      WithLp.toLp 2 (Lp.LpToLpOfMeasureLeSMul hc hν f,E) ∈ l2RelaxedGraph ν →
      ‖Lp.LpToLpOfMeasureLeSMul hc hν D‖ ≤ ‖E‖ := by
  intro E hE
  let S := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hd hm
  have hEm : WithLp.toLp 2 (f,S E) ∈ l2RelaxedGraph m := by
    have H := relaxedGraph_changeMeasure hd hm hE
    rwa [changeLp_inverse hc hd hν hm] at H
  have hle := pointwise_minimal_relaxedGradient hfinite hD hmin hEm
  have hEn := (relaxedGraph_isUpperGradient (hfinite.of_measure_le_smul hc hν) hE).2.1
  have hDn := (relaxedGraph_isUpperGradient hfinite hD).2.1
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le hle,
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le hDn,
    Lp.coeFn_LpToLpOfMeasureLeSMul hc hν D,hEn,
    (Measure.absolutelyContinuous_of_le_smul hν).ae_eq
      (Lp.coeFn_LpToLpOfMeasureLeSMul hd hm E)] with x hdx hdpos ht hen hs
  change D x ≤ (S E) x at hdx
  change 0 ≤ D x at hdpos
  change 0 ≤ E x at hen
  change (S E) x = E x at hs
  rw [Real.norm_eq_abs,Real.norm_eq_abs,ht,abs_of_nonneg hdpos,abs_of_nonneg hen]
  exact hdx.trans_eq hs

lemma cheegerEnergy_relaxed_comparable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    (hfinite : FiniteOnBoundedSets m) {c d : ℝ≥0∞} (hc : c ≠ ∞) (hd : d ≠ ∞)
    (hν : ν ≤ c • m) (hm : m ≤ d • ν)
    {f D : Lp ℝ 2 m} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m)
    (hmin : ∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖) :
    cheegerEnergy ν (f : X → ℝ) =
      ENNReal.ofReal (‖Lp.LpToLpOfMeasureLeSMul hc hν D‖^2/2) := by
  let T := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hc hν
  rw [← cheegerEnergy_congr_ae (Lp.coeFn_LpToLpOfMeasureLeSMul hc hν f)]
  have hDν := relaxedGraph_changeMeasure hc hν hD
  have hle := relaxedGraph_energy_le (p := WithLp.toLp 2 (T f,T D)) hDν
  obtain ⟨E,hE,_,he⟩ := exists_relaxedGradient_energy_eq
    (hle.trans_lt ENNReal.ofReal_lt_top)
  apply le_antisymm hle
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have H := relaxedGradient_minimal_comparable hfinite hc hd hν hm hD hmin E hE
  change ‖T D‖^2/2 ≤ ‖E‖^2/2
  change ‖T D‖ ≤ ‖E‖ at H
  nlinarith [norm_nonneg E,norm_nonneg (T D)]
end WeakHessian

end
end InlinedFile0

end OAI
