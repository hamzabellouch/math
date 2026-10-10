import OAI.Analysis.CircleDomains.Probability.PathLengthMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

/-! The arclength measures form a Borel kernel on rectifiable paths. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathLengthMeasure :
    Measurable (pathLengthMeasure (X := X)) := by
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc PathTime))
    (isPiSystem_Ioc id id)
  · rintro s ⟨a, b, hab, rfl⟩
    have hm : Measurable (fun γ : RectifiablePath X => eVariationOn γ.val (Icc a b)) :=
      (measurable_pathVariation (X := X) (Icc a b)).comp measurable_subtype_coe
    simpa only [pathLengthMeasure_Ioc _ hab.le] using hm
  · have hm : Measurable (fun γ : RectifiablePath X => eVariationOn γ.val univ) :=
      (measurable_pathVariation (X := X) univ).comp measurable_subtype_coe
    simpa only [pathLengthMeasure_univ] using hm

def pathLengthKernel : ProbabilityTheory.Kernel (RectifiablePath X) PathTime where
  toFun := pathLengthMeasure
  measurable' := measurable_pathLengthMeasure

@[simp] theorem pathLengthKernel_apply (γ : RectifiablePath X) :
    pathLengthKernel γ = pathLengthMeasure γ := rfl

instance (γ : RectifiablePath X) : IsFiniteMeasure (pathLengthKernel γ) := by
  change IsFiniteMeasure (pathLengthMeasure γ)
  infer_instance

end CircleDomainRigidity

end

end OAI
