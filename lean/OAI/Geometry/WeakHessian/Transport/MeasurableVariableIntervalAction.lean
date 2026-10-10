import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.EvalRealCoe

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

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma measurable_variable_interval_action {a : Curve X × ℝ → ℝ≥0∞} (ha : Measurable a) (s : ℝ) :
    Measurable (fun p : Curve X × ℝ => ∫⁻ r in uIcc s p.2, a (p.1,r)) := by
  let H : (Curve X × ℝ) × ℝ → ℝ≥0∞ := fun p =>
    if p.2 ∈ uIcc s p.1.2 then a (p.1.1,p.2) else 0
  have hset : MeasurableSet {p : (Curve X × ℝ) × ℝ | p.2 ∈ uIcc s p.1.2} := by
    apply MeasurableSet.inter
    · exact measurableSet_le (measurable_const.min measurable_fst.snd) measurable_snd
    · exact measurableSet_le measurable_snd (measurable_const.max measurable_fst.snd)
  have hH : Measurable H := Measurable.ite hset
    (ha.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_const
  have hEq : (fun p : Curve X × ℝ => ∫⁻ r, H (p,r)) =
      (fun p : Curve X × ℝ => ∫⁻ r in uIcc s p.2, a (p.1,r)) := by
    funext p
    exact lintegral_indicator (s := uIcc s p.2) measurableSet_uIcc (fun r => a (p.1,r))
  rw [← hEq]
  exact hH.lintegral_prod_right

lemma IsLocalWeakUpperGradient.ae_ae_subinterval_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : Measurable f) (hDm : Measurable D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) (s : Time) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ENNReal.ofReal |f (evalReal γ t) - f (γ s)| ≤
        ∫⁻ r in uIcc (s : ℝ) t,
          ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r := by
  let : IsProbabilityMeasure π := hπ.1
  have ham : Measurable (fun p : Curve X × ℝ =>
      ENNReal.ofReal (D (evalReal p.1 p.2)) * metricSpeed p.1 p.2) :=
    (hDm.comp continuous_evalReal.measurable).ennreal_ofReal.mul measurable_metricSpeed
  apply (Measure.ae_ae_comm (p := fun γ t =>
    ENNReal.ofReal |f (evalReal γ t) - f (γ s)| ≤
      ∫⁻ r in uIcc (s : ℝ) t,
        ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r) ?_).mpr
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    let t' : Time := ⟨t,ht⟩
    rcases lt_trichotomy (s : ℝ) t with h|h|h
    · filter_upwards [hD.ae_subinterval_le hf.aemeasurable hπ hb s t' h] with γ hγ
      simpa only [uIcc_of_le h.le, ← evalReal_coe γ t'] using hγ
    · have heq : t' = s := Subtype.ext h.symm
      have hev : ∀ γ : Curve X, evalReal γ t = γ s := fun γ => by
        exact (evalReal_coe γ t').trans (congrArg γ heq)
      exact ae_of_all _ fun γ => by rw [hev, sub_self, abs_zero, ENNReal.ofReal_zero]; exact bot_le
    · have hh := hD.ae_subinterval_le hf.aemeasurable hπ hb t' s h
      filter_upwards [hh] with γ hγ
      simpa only [uIcc_of_ge h.le, ← evalReal_coe γ t', abs_sub_comm] using hγ
  · exact measurableSet_le
      ((hf.comp continuous_evalReal.measurable).sub
        (hf.comp ((continuous_eval_const s).measurable.comp measurable_fst))).abs.ennreal_ofReal
      (measurable_variable_interval_action ham s)

end WeakHessian

end
end InlinedFile0

end OAI
