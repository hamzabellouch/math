import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.EvalRealCoe
import OAI.Geometry.WeakHessian.LocalBounds.ClampTimeVal
import OAI.Geometry.WeakHessian.Transport.KineticAction
import OAI.Geometry.WeakHessian.Transport.MapCompProdComap

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def halfTime (t : Time) : Time := ⟨(t:ℝ)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩
def rightTime (t : Time) : Time := ⟨((t:ℝ)+1)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩
lemma joinCurve_halfTime (γ η : Curve X) (h : γ timeOne = η timeZero) (t : Time) :
    joinCurve γ η h (halfTime t) = γ t := by
  rw [joinCurve_apply_left _ _ _ _ (by dsimp [halfTime]; have := t.2.2; linarith)]
  dsimp [halfTime]
  rw [show 2*((t:ℝ)/2) = (t:ℝ) by ring, evalReal_coe]

lemma joinCurve_rightTime (γ η : Curve X) (h : γ timeOne = η timeZero) (t : Time) :
    joinCurve γ η h (rightTime t) = η t := by
  rw [joinCurve_apply_right _ _ _ _ (by dsimp [rightTime]; have := t.2.1; linarith)]
  dsimp [rightTime]
  rw [show 2*(((t:ℝ)+1)/2)-1 = (t:ℝ) by ring, evalReal_coe]

lemma kineticAction_join (γ η : Curve X) (h : γ timeOne = η timeZero) :
    kineticAction (joinCurve γ η h) ≤ 2*(kineticAction γ+kineticAction η) := by
  by_cases hγ : controlNorm γ = ∞
  · simp [kineticAction, hγ]
  by_cases hη : controlNorm η = ∞
  · simp [kineticAction, hη]
  let A := (controlNorm γ).toReal
  let B := (controlNorm η).toReal
  have hA : HasControlBound γ A := (controlNorm_le_iff ENNReal.toReal_nonneg).mp (by rw [ENNReal.ofReal_toReal hγ])
  have hB : HasControlBound η B := (controlNorm_le_iff ENNReal.toReal_nonneg).mp (by rw [ENNReal.ofReal_toReal hη])
  have H := controlNorm_le (hasControlBound_join h hA hB)
  have hnonneg : 0 ≤ 2*(A^2+B^2) := by positivity
  calc
    kineticAction (joinCurve γ η h) ≤ (ENNReal.ofReal (Real.sqrt (2*(A^2+B^2))))^2 :=
      pow_le_pow_left₀ bot_le H 2
    _ = ENNReal.ofReal (2*(A^2+B^2)) := by rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]
    _ = 2*(kineticAction γ+kineticAction η) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_pow ENNReal.toReal_nonneg]
      simp only [ENNReal.ofReal_toReal hγ, ENNReal.ofReal_toReal hη, ENNReal.ofReal_ofNat, kineticAction]

lemma exists_join_plan [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
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

end
end InlinedFile0

end OAI
