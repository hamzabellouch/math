import OAI.Analysis.CircleDomains.Modulus.PathVariation
import Mathlib.MeasureTheory.Measure.Stieltjes

namespace OAI

/-! The arclength measure of an ordinary rectifiable continuous metric path.
It is atomless and assigns each interval its actual metric variation. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

abbrev RectifiablePath (X : Type*) [MetricSpace X] :=
  {γ : C(PathTime, X) // BoundedVariationOn γ univ}

def pathLengthFunction (γ : RectifiablePath X) : StieltjesFunction PathTime where
  toFun t := variationOnFromTo γ.val univ ⊥ t
  mono' := monotoneOn_univ.mp
    (variationOnFromTo.monotoneOn γ.property.locallyBoundedVariationOn (mem_univ _))
  right_continuous' _t := γ.property.continuousWithinAt_variationOnFromTo_Ici
    γ.val.continuous.continuousAt.continuousWithinAt

def pathLengthMeasure (γ : RectifiablePath X) : Measure PathTime :=
  (pathLengthFunction γ).measure

theorem continuous_pathLengthFunction (γ : RectifiablePath X) :
    Continuous (pathLengthFunction γ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (γ.property.continuousAt_variationOnFromTo_iff ⊥ t).mpr γ.val.continuous.continuousAt

instance (γ : RectifiablePath X) : IsFiniteMeasure (pathLengthMeasure γ) :=
  (pathLengthFunction γ).isFiniteMeasure_of_forall_abs_le
    (fun _ => variationOnFromTo.abs_le_eVariationOn γ.property)

instance (γ : RectifiablePath X) : NullSingletonClass (pathLengthMeasure γ) := by
  constructor
  intro t
  rw [pathLengthMeasure, StieltjesFunction.measure_singleton]
  have ht : ContinuousWithinAt (pathLengthFunction γ) (Iic t) t :=
    (continuous_pathLengthFunction γ).continuousAt.continuousWithinAt
  rw [ht.leftLim_eq, sub_self, ENNReal.ofReal_zero]

theorem pathLengthMeasure_Ioc (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure γ (Ioc a b) = eVariationOn γ.val (Icc a b) := by
  rw [pathLengthMeasure, StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (variationOnFromTo γ.val univ ⊥ b -
    variationOnFromTo γ.val univ ⊥ a) = _
  rw [variationOnFromTo.sub_right γ.property.locallyBoundedVariationOn
    (mem_univ _) (mem_univ _) (mem_univ _), variationOnFromTo.eq_of_le _ _ hab,
    univ_inter, ENNReal.ofReal_toReal]
  exact γ.property.mono (subset_univ _)

theorem pathLengthMeasure_Icc (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure γ (Icc a b) = eVariationOn γ.val (Icc a b) := by
  rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure γ))]
  exact pathLengthMeasure_Ioc γ hab

theorem pathLengthMeasure_univ (γ : RectifiablePath X) :
    pathLengthMeasure γ univ = eVariationOn γ.val univ := by
  simpa only [Icc_bot_top] using pathLengthMeasure_Icc γ (bot_le : (⊥ : PathTime) ≤ ⊤)

end CircleDomainRigidity

end

end OAI
