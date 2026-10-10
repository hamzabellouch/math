import Mathlib
import OAI.Geometry.WeakHessian.Transport.AeActionData
import OAI.Geometry.WeakHessian.Transport.ActionDistPrimitiveValues
import OAI.Geometry.WeakHessian.Transport.MeasurableVariableIntervalAction

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
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.ae_exists_ac_representative_measurable {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : Measurable f) (hDm : Measurable D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π, ∃ q : ℝ → ℝ,
      AbsolutelyContinuousOnInterval q 0 1 ∧ q 0 = f (γ timeZero) ∧ q 1 = f (γ timeOne) ∧
      (q =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun t => f (evalReal γ t)) ∧
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv q t| ≤ ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : Nonempty Time := ⟨timeZero⟩
  let d : ℕ → Time := fun n => match n with
    | 0 => timeZero
    | 1 => timeOne
    | n + 2 => TopologicalSpace.denseSeq Time n
  have hd : DenseRange d := by
    apply DenseRange.of_comp (g := fun n => n + 2)
    exact TopologicalSpace.denseRange_denseSeq Time
  have hall : ∀ᵐ γ ∂π, ∀ i : ℕ, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ENNReal.ofReal |f (evalReal γ t) - f (γ (d i))| ≤
        ∫⁻ r in uIcc (d i : ℝ) t,
          ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r :=
    ae_all_iff.mpr fun i => hD.ae_ae_subinterval_le hf hDm hπ hb (d i)
  filter_upwards [hD.ae_action_data hπ hb,
    hD.ae_dense_subinterval_le hf.aemeasurable hπ hb d, hall] with γ hDa hDb hp
  have hDb' : ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |f (evalReal γ (d j)) - f (evalReal γ (d i))| ≤
        ∫⁻ t in Icc (d i : ℝ) (d j : ℝ),
          ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
    simpa only [evalReal_coe] using hDb
  obtain ⟨q,hq,heq⟩ := WeakHessianCalculus.exists_ac_representative
    (q := fun t => f (evalReal γ t)) hDa.1 hDa.2 d hDb'
  have hqd : ∀ i, q (d i) = f (γ (d i)) := by simpa only [evalReal_coe] using heq
  refine ⟨q,hq,hqd 0,hqd 1,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr hp, ae_restrict_mem measurableSet_Icc] with t ht htm
    exact WeakHessianCalculus.eq_of_dense_action_bounds hq hDa.1 hDa.2 d hd htm
      (by simpa only [hqd] using ht)
  · exact WeakHessianCalculus.ae_deriv_le_of_dense_action hq hDa.1 hDa.2 d hd
      (by simpa only [hqd] using hDb)

lemma IsLocalWeakUpperGradient.ae_exists_ac_representative {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π, ∃ q : ℝ → ℝ,
      AbsolutelyContinuousOnInterval q 0 1 ∧ q 0 = f (γ timeZero) ∧ q 1 = f (γ timeOne) ∧
      (q =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun t => f (evalReal γ t)) ∧
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv q t| ≤ ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  have hDm := hD.1.aemeasurable
  have hD' := hD.congr_ae hf.ae_eq_mk hDm.ae_eq_mk
  filter_upwards [hD'.ae_exists_ac_representative_measurable hf.measurable_mk
      hDm.measurable_mk hπ hb, hπ.ae_eval_of_ae hf.ae_eq_mk timeZero,
      hπ.ae_eval_of_ae hf.ae_eq_mk timeOne, hπ.ae_ae_eval_of_ae hf.ae_eq_mk,
      hπ.ae_ae_eval_of_ae hDm.ae_eq_mk] with γ hγ h0 h1 heq hDeq
  obtain ⟨q,hq,hq0,hq1,hqa,hqd⟩ := hγ
  refine ⟨q,hq,hq0.trans h0.symm,hq1.trans h1.symm,hqa.trans (Filter.EventuallyEq.symm heq),?_⟩
  filter_upwards [hqd,hDeq] with t ht hDt
  rwa [← hDt] at ht

end WeakHessian

end
end InlinedFile0

end OAI
