import Mathlib
import OAI.Probability.Perceptron.Cascade.DecoratedWeightedTotal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace SphericalPerceptronFreeEnergy
lemma finiteCascadeLogRecursion_add_constant {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S→X) (H : X→ℝ) (k : ℕ) (z : Fin k→ℝ)
    (hz : ∀ i,0<z i) (hi : finiteCascadeFractionalIntegrable ν step H k z) (c : ℝ) (x : X) :
    finiteCascadeLogRecursion ν step k z (fun x=>c+H x) x=
      c+finiteCascadeLogRecursion ν step k z H x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [finiteCascadeLogRecursion,ih _ (fun i=>hz i.succ) hi.2,fractionalLogMoment]
    simp_rw [mul_add,Real.exp_add]
    rw [integral_const_mul,Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos (hi.1 x)).ne',Real.log_exp]
    field_simp [(hz 0).ne']

lemma finiteCascadeFractionalIntegrable_add_constant {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S→X) (H : X→ℝ) (k : ℕ) (z : Fin k→ℝ)
    (hz : ∀ i,0<z i) (hi : finiteCascadeFractionalIntegrable ν step H k z) (c : ℝ) :
    finiteCascadeFractionalIntegrable ν step (fun x=>c+H x) k z := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨?_,ih _ (fun i=>hz i.succ) hi.2⟩
    intro x
    simp only [finiteCascadeLogRecursion_add_constant ν step H k _ (fun i=>hz i.succ) hi.2 c,mul_add,Real.exp_add]
    exact (hi.1 x).const_mul _
end SphericalPerceptronFreeEnergy

end

end OAI
