import Mathlib
import OAI.Geometry.WeakHessian.Transport.DynamicActionBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set MeasureTheory Filter
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
lemma exists_join_plan_polish [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] (μ ν : Measure (Curve X)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hpush : μ.map (fun γ => γ timeOne) = ν.map (fun γ => γ timeZero)) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ t : Time, π.map (fun γ => γ (halfTime t)) = μ.map (fun γ => γ t)) ∧
      (∀ t : Time, π.map (fun γ => γ (rightTime t)) = ν.map (fun γ => γ t)) ∧
      (∫⁻ γ, kineticAction γ ∂π) ≤ 2*((∫⁻ γ, kineticAction γ ∂μ)+(∫⁻ γ, kineticAction γ ∂ν)) := by
  let : Nonempty (Curve X) := ⟨ContinuousMap.const Time (Classical.arbitrary X)⟩
  let E := {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero}
  have hE : MeasurableSet E := isClosed_joinable.measurableSet
  obtain ⟨q,hqp,hq0,hq1,hqE⟩ := WeakHessianTransport.exists_fiber_gluing_supported μ ν
    (fun γ => γ timeOne) (fun γ => γ timeZero) (continuous_eval_const _).measurable
    (continuous_eval_const _).measurable hpush
  let := hqp
  let qs : Measure (Joinable X) := q.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : Joinable X → Curve X × Curve X) :=
    MeasurableEmbedding.subtype_coe hE
  have hsupp : ∀ᵐ p ∂q, p ∈ range (Subtype.val : Joinable X → Curve X×Curve X) := by
    simpa only [Subtype.range_coe_subtype, mem_ofPred_eq] using hqE
  let : IsProbabilityMeasure qs := hemb.isProbabilityMeasure_comap hsupp
  have hqs : qs.map Subtype.val = q := by
    rw [hemb.map_comap, Measure.restrict_eq_self_of_ae_mem hsupp]
  have hqsfst : qs.map (fun p => p.1.1) = μ := by
    rw [← hq0, ← hqs, Measure.map_map measurable_fst hemb.measurable]
    rfl
  have hqssnd : qs.map (fun p => p.1.2) = ν := by
    rw [← hq1, ← hqs, Measure.map_map measurable_snd hemb.measurable]
    rfl
  have hfstm : Measurable (fun p : Joinable X => p.1.1) := measurable_fst.comp measurable_subtype_coe
  have hsndm : Measurable (fun p : Joinable X => p.1.2) := measurable_snd.comp measurable_subtype_coe
  let π := qs.map joinMap
  have hjm : Measurable (joinMap (X := X)) := lipschitz_joinMap.continuous.measurable
  let : IsProbabilityMeasure π := inferInstance
  refine ⟨π,inferInstance,?_,?_,?_⟩
  · intro t
    change (qs.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hqsfst,
      Measure.map_map (g := fun γ : Curve X => γ t) (continuous_eval_const t).measurable hfstm]
    congr 1
    funext p
    exact joinCurve_halfTime _ _ _ t
  · intro t
    change (qs.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hqssnd,
      Measure.map_map (g := fun γ : Curve X => γ t) (continuous_eval_const t).measurable hsndm]
    congr 1
    funext p
    exact joinCurve_rightTime _ _ _ t
  · have ha := (lowerSemicontinuous_kineticAction (X := X)).measurable
    change (∫⁻ γ, kineticAction γ ∂qs.map joinMap) ≤ _
    rw [lintegral_map ha hjm]
    calc
      (∫⁻ p, kineticAction (joinMap p) ∂qs) ≤
          ∫⁻ p, 2*(kineticAction p.1.1+kineticAction p.1.2) ∂qs :=
        lintegral_mono fun p => kineticAction_join _ _ p.2
      _ = 2*((∫⁻ p, kineticAction p.1.1 ∂qs)+(∫⁻ p, kineticAction p.1.2 ∂qs)) := by
        have hsum : Measurable (fun p : Joinable X => kineticAction p.1.1+kineticAction p.1.2) :=
          (ha.comp hfstm).add (ha.comp hsndm)
        rw [lintegral_const_mul (μ := qs) 2 hsum]
        exact congrArg (fun v : ℝ≥0∞ => 2*v) (lintegral_add_aux (ha.comp hfstm) (ha.comp hsndm))
      _ = _ := by
        rw [← lintegral_map (μ := qs) ha hfstm, hqsfst,
          ← lintegral_map (μ := qs) ha hsndm, hqssnd]

end WeakHessian

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]

lemma exists_grid_plan_polish (n : ℕ) (μ : Time → Measure X) {C : ℝ} (hC : 0 ≤ C)
    (h : DynamicActionBound μ C) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ t ∈ dyadicTimes n, π.map (fun γ => γ t) = μ t) ∧
      (∫⁻ γ, kineticAction γ ∂π) ≤ ENNReal.ofReal C := by
  induction n generalizing μ C with
  | zero =>
    obtain ⟨π,hπ,h0,h1,hb⟩ := h timeZero timeOne
    refine ⟨π,hπ,?_,?_⟩
    · intro t ht
      rcases ht with rfl | ht
      · exact h0
      · have he : t = timeOne := ht
        simpa only [he] using h1
    · simpa only [Subtype.dist_eq, timeZero, timeOne, Real.dist_eq, zero_sub,
        abs_neg, abs_one, one_pow, mul_one] using hb
  | succ n ih =>
    obtain ⟨πL,hL,hLm,hLA⟩ := ih (μ ∘ halfTime) (div_nonneg hC (by norm_num)) h.half
    obtain ⟨πR,hR,hRm,hRA⟩ := ih (μ ∘ rightTime) (div_nonneg hC (by norm_num)) h.right
    let := hL
    let := hR
    have hmatch : πL.map (fun γ => γ timeOne) = πR.map (fun γ => γ timeZero) := by
      rw [hLm _ (one_mem_dyadicTimes n),hRm _ (zero_mem_dyadicTimes n)]
      simp only [Function.comp_apply,halfTime_one_eq_rightTime_zero]
    obtain ⟨π,hπ,hπL,hπR,hπA⟩ := exists_join_plan_polish πL πR hmatch
    refine ⟨π,hπ,?_,?_⟩
    · intro t ht
      rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
      · rw [hπL,hLm _ hs]; rfl
      · rw [hπR,hRm _ hs]; rfl
    · calc
        (∫⁻ γ, kineticAction γ ∂π) ≤ 2*((∫⁻ γ, kineticAction γ ∂πL)+(∫⁻ γ, kineticAction γ ∂πR)) := hπA
        _ ≤ 2*(ENNReal.ofReal (C/4)+ENNReal.ofReal (C/4)) := mul_le_mul_right (add_le_add hLA hRA) 2
        _ = ENNReal.ofReal C := by
          rw [← ENNReal.ofReal_add (div_nonneg hC (by norm_num)) (div_nonneg hC (by norm_num)),
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          congr 1
          ring

end WeakHessian

end
end InlinedFile0

end OAI
