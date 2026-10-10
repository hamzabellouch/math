import OAI.Analysis.CircleDomains.Selection.RayIndexCrossings
import OAI.Analysis.CircleDomains.Probability.MeasurableArcIndex
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

namespace OAI

/-! Borel dependence of the compactified rays on the actual arc sample.
No measurable choice of Schoenflies homeomorphisms is used. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

variable (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)

theorem continuous_initialArcAngles_family (c : PathTime) (hc : c < ⊤) :
    Continuous (fun γ : K => initialArcAngles puncturedArgument γ.val
      (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply puncturedArgument.continuous.comp
  apply Continuous.subtype_mk
  exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_snd.mul continuous_const))

theorem measurable_diskRayAngle_family (t : DiskRayTime) :
    Measurable (fun γ : K => diskRayAngle γ.val (hKS γ.property).1
      (hKS γ.property).2.2.1 t) := by
  have hs : Measurable (fun γ : K => circleRepresentative (normalizedArgument (γ.val 0))) :=
    measurable_circleRepresentative.comp (measurable_normalizedArgument.comp
      ((continuous_eval_const 0).comp continuous_subtype_val).measurable)
  have hi := continuous_circlePathIncrement.comp (continuous_initialArcAngles_family K hKS t.val t.property)
  convert hs.add hi.measurable using 1
  funext γ
  exact diskRayAngle_eq_increment _ _ _ t

theorem measurable_translatedRay_family (k : ℤ) (t : DiskRayTime) :
    Measurable (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).curve t) := by
  have ha := measurable_diskRayAngle_family K hKS t
  have hd : Measurable (fun γ : K => diskRayDepth γ.val t) :=
    (((continuous_eval_const t.val).comp continuous_subtype_val).measurable.norm.log).neg
  exact ((Complex.continuous_ofReal.measurable.comp ha).add
    ((Complex.continuous_ofReal.measurable.comp hd).mul_const Complex.I)).add_const (k : ℂ)

theorem measurable_translatedCrosscut_family (k : ℤ) :
    Measurable (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut.toContinuousMap) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  by_cases ht : t < ⊤
  · have hc : Measurable halfPlaneDisk := by
      unfold halfPlaneDisk
      fun_prop
    have hm := hc.comp (measurable_translatedRay_family K hKS k ⟨t, ht⟩)
    convert hm using 1
    funext γ
    change (translatedHalfPlaneRay γ.val (hKS γ.property) k).compactify t = halfPlaneDisk _
    rw [HalfPlaneRay.compactify, dite_eq_left ht]
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    have heq : (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut.toContinuousMap ⊤) =
        fun _ => (1 : ℂ) := by
      funext γ
      exact HalfPlaneRay.compactify_top _
    rw [heq]
    exact measurable_const

end CircleDomainRigidity

end

end OAI
