import Mathlib
import OAI.Probability.Perceptron.Cascade.DecoratedWeightedTotal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma finiteCascadeLogRecursion_transport {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (a : X×S→X) (b : Y×T→Y) (hb : Measurable b)
    (φ : X→Y) (r : S→T) (hr : MeasurePreserving r (ν:Measure S) (ρ:Measure T))
    (he : ∀ x s,φ (a (x,s))=b (φ x,r s))
    (H : Y→ℝ) (hH : Measurable H) (k : ℕ) (z : Fin k→ℝ) (x : X) :
    finiteCascadeLogRecursion ν a k z (H ∘ φ) x=
      finiteCascadeLogRecursion ρ b k z H (φ x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [finiteCascadeLogRecursion,fractionalLogMoment,ih,he]
    congr 2
    have hm : Measurable (fun t=>Real.exp (z 0 * finiteCascadeLogRecursion ρ b k (fun i=>z i.succ) H (b (φ x,t)))) := (((finiteCascadeLogRecursion_measurable ρ b hb k (fun i=>z i.succ) hH).comp
      (hb.comp (measurable_const.prodMk measurable_id))).const_mul (z 0)).exp
    rw [←hr.map_eq,integral_map hr.measurable.aemeasurable hm.aestronglyMeasurable]

lemma finiteCascadeFractionalIntegrable_transport {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (a : X×S→X) (b : Y×T→Y) (hb : Measurable b)
    (φ : X→Y) (r : S→T) (hr : MeasurePreserving r (ν:Measure S) (ρ:Measure T))
    (he : ∀ x s,φ (a (x,s))=b (φ x,r s))
    (H : Y→ℝ) (hH : Measurable H) (k : ℕ) (z : Fin k→ℝ)
    (hi : finiteCascadeFractionalIntegrable ρ b H k z) :
    finiteCascadeFractionalIntegrable ν a (H ∘ φ) k z := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨?_,ih _ hi.2⟩
    intro x
    simp only [finiteCascadeLogRecursion_transport ν ρ a b hb φ r hr he H hH,he]
    exact (hr.integrable_comp (hi.1 (φ x)).aestronglyMeasurable).mpr (hi.1 (φ x))
end SphericalPerceptronFreeEnergy

end

end OAI
