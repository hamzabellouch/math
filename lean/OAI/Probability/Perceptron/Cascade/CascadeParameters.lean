import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianMarkRecursion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {P X S : Type} [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace S]

def parameterMarkStep (step : X×S → X) : (P×X)×S → P×X :=
  fun a => (a.1.1,step (a.1.2,a.2))

lemma parameterMarkStep_measurable {step : X×S → X} (hs : Measurable step) :
    Measurable (parameterMarkStep (P := P) step) :=
  (measurable_fst.comp measurable_fst).prodMk
    (hs.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma decoratedTerminalTotalE_parameter (step : X×S → X) (H : P → X → ℝ)
    (n : ℕ) (p : P) (x : X) (η : DecoratedCascade S n) :
    decoratedTerminalTotalE (parameterMarkStep step) (Function.uncurry H) n ((p,x),η)=
      decoratedTerminalTotalE step (H p) n (x,η) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    apply lintegral_congr
    intro q
    congr 1
    exact ih (step (x,q.2.1)) q.2.2

lemma decoratedTerminalTotal_parameter (step : X×S → X) (H : P → X → ℝ)
    (n : ℕ) (p : P) (x : X) (η : DecoratedCascade S n) :
    decoratedTerminalTotal (parameterMarkStep step) (Function.uncurry H) n ((p,x),η)=
      decoratedTerminalTotal step (H p) n (x,η) :=
  congrArg ENNReal.toReal (decoratedTerminalTotalE_parameter step H n p x η)

end

variable {P E : Type} [MeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma gaussianLinearCascadeLog_parameter_measurable
    (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {H : P → E → ℝ} (hH : Measurable (Function.uncurry H)) (k : ℕ) (z : Fin k → ℝ) :
    Measurable (fun a : P × (E×DecoratedCascade E k) =>
      gaussianLinearCascadeLog A R (H a.1) k a.2) := by
  let step := gaussianLinearMarkStep A
  let V := fun p : P => fun x : ℕ → E => H p (x 0)
  have hV : Measurable (Function.uncurry V) := hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  let T := fun a : P × (E×DecoratedCascade E k) =>
    ((a.1,fun _ : ℕ => R a.2.1),a.2.2)
  have hT : Measurable T :=
    (measurable_fst.prodMk (Measurable.of_eval (fun _ =>
      R.measurable.comp (measurable_fst.comp measurable_snd)))).prodMk
        (measurable_snd.comp measurable_snd)
  let ν : ProbabilityMeasure E := gaussianMarkLaw
  have hs : Measurable step := gaussianLinearMarkStep_measurable A
  have h1 := (decoratedTerminalTotal_measurable ν (parameterMarkStep step)
    (parameterMarkStep_measurable hs) hV k z).comp hT
  have h0 := (decoratedTerminalTotal_measurable ν (parameterMarkStep step)
    (parameterMarkStep_measurable hs) (H := Function.uncurry (fun (_ : P) (_ : ℕ → E) => (0:ℝ)))
    measurable_const k z).comp hT
  have he (a : P × (E×DecoratedCascade E k)) :
      gaussianLinearCascadeLog A R (H a.1) k a.2=
        Real.log (decoratedTerminalTotal (parameterMarkStep step) (Function.uncurry V) k (T a)/
          decoratedTerminalTotal (parameterMarkStep step) (Function.uncurry (fun (_ : P) (_ : ℕ → E) => (0:ℝ))) k (T a)) := by
    rw [decoratedTerminalTotal_parameter,decoratedTerminalTotal_parameter]
    rfl
  simp_rw [he]
  exact (h1.div h0).log
end SphericalPerceptronFreeEnergy
end

end OAI
