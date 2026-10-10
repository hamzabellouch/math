import OAI.Analysis.CircleDomains.Reflection.ReflectionTileAction
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

namespace OAI

/-! Coefficient transport through reduced reflection words. The pointwise
involution is proved before gluing the disjoint geometric copies. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X]

def reflectionCoefficientWord (R : I → X ≃ₜ X) (V : I → X → ℂ → ℂ) :
    List I → (X → ℂ) → X → ℂ
  | [],f => f
  | i::w,f => fun x => V i x (reflectionCoefficientWord R V w f (R i x))

lemma reflectionCoefficientWord_bound (R : I → X ≃ₜ X) (V : I → X → ℂ → ℂ)
    (hV : ∀i x a,‖V i x a‖=‖a‖) (f : X → ℂ) {k : ℝ}
    (hf : ∀x,‖f x‖≤k) (w : List I) :
    ∀x,‖reflectionCoefficientWord R V w f x‖≤k := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    intro x
    change ‖V i x (reflectionCoefficientWord R V w f (R i x))‖≤k
    rw [hV]
    exact ih _

lemma reflectionCoefficientWord_measurable [MeasurableSpace X] [BorelSpace X]
    (R : I → X ≃ₜ X) (V : I → X → ℂ → ℂ)
    (hV : ∀i,Measurable (fun p : X × ℂ => V i p.1 p.2))
    (f : X → ℂ) (hf : Measurable f) (w : List I) :
    Measurable (reflectionCoefficientWord R V w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (hV i).comp (measurable_id.prodMk (ih.comp (R i).continuous.measurable))

lemma reflectionCoefficientWord_reduceStep [DecidableEq I]
    (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i)) (V : I → X → ℂ → ℂ)
    (hV : ∀i x a,V i x (V i (R i x) a)=a) (f : X → ℂ) (i : I) (w : List I) (x : X) :
    reflectionCoefficientWord R V (reflectionReduceStep i w) f x=
      V i x (reflectionCoefficientWord R V w f (R i x)) := by
  cases w with
  | nil => rfl
  | cons j w =>
    by_cases hij : i=j
    · subst j
      simp only [reflectionReduceStep,ite_true,reflectionCoefficientWord]
      rw [hR i]
      exact (hV i x _).symm
    · simp only [reflectionReduceStep,ite_eq_right hij,reflectionCoefficientWord]

end CircleDomainRigidity

end

end OAI
