import Mathlib
import OAI.Probability.SphericalField.Cascade.Descendants

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

def decoratedCascadeTransform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → StableCascade n
  | 0, _, _ => ()
  | n+1, F, p => (markedStableCountKernel p.2).map (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (p.1,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,q.2.1),q.2.2)))

lemma decoratedCascadeTransform_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) : Measurable (decoratedCascadeTransform step n F) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let H : X×(ℝ×(S×DecoratedCascade S n)) → ℝ×StableCascade n := fun p =>
      (p.2.1+F 0 (p.1,p.2.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,p.2.2.1),p.2.2.2))
    have hH : Measurable H :=
      (measurable_snd.fst.add ((hF 0).comp (measurable_fst.prodMk measurable_snd.snd.fst))).prodMk
        ((ih (fun i => F i.succ) (fun i => hF i.succ)).comp
          ((hstep.comp (measurable_fst.prodMk measurable_snd.snd.fst)).prodMk measurable_snd.snd.snd))
    exact countKernel_parameter_map_measurable H hH

theorem decoratedCascadeTransform_law {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)).map
      (fun η => decoratedCascadeTransform step n F (x,η)) = cascadeLaw n z := by
  induction n generalizing x with
  | zero =>
    change Measure.map (fun _ : Unit => ()) (Measure.dirac ()) = Measure.dirac ()
    exact Measure.map_dirac ()
  | succ n ih =>
    let ρ : Measure (DecoratedCascade S n) := decoratedCascadeLaw ν n (fun i => z i.succ)
    let θ : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
    let T : S×DecoratedCascade S n → StableCascade n := fun p =>
      decoratedCascadeTransform step n (fun i => F i.succ) (step (x,p.1),p.2)
    have hT : Measurable T :=
      (decoratedCascadeTransform_measurable step hstep n _ (fun i => hF i.succ)).comp
        ((hstep.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have ht : ∀ s, ρ.map (fun c => T (s,c)) = θ := fun s =>
      ih (fun i => z i.succ) (fun i => hz0 i.succ) (fun i => hz1 i.succ)
        (fun i => F i.succ) (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ) (step (x,s))
    let G : ℝ×(S×DecoratedCascade S n) → ℝ×StableCascade n :=
      fun p => (p.1+F 0 (x,p.2.1),T p.2)
    change (poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ((ν : Measure S).prod ρ))).map
      (fun η => (markedStableCountKernel η).map G) = poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod θ)
    calc
      _ = (poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ((ν : Measure S).prod ρ))).map
            (Measure.map G) := by
        apply Measure.map_congr
        filter_upwards [markedStable_regular ((ν : Measure S).prod ρ) (hz0 0) (hz1 0)] with η hη
        rw [markedStableCountKernel_eq η hη.1 hη.2]
      _ = _ := stablePoisson_descendant_transform (ν : Measure S) ρ θ (hz0 0).le T hT ht
        ((hF 0).comp (measurable_const.prodMk measurable_id)) (hI 0 x) (hM 0 x)

lemma decoratedCascadeTransform_root_independent {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (μ : Measure X) [SFinite μ]
    (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) :
    (μ.prod (decoratedCascadeLaw ν n z)).map (fun p => (p.1,decoratedCascadeTransform step n F p)) =
      μ.prod (cascadeLaw n z) := by
  apply descendant_transform_independent _ _ _ _ (decoratedCascadeTransform_measurable step hstep n F hF)
  exact decoratedCascadeTransform_law ν step hstep n z hz0 hz1 F hF hI hM

end SphericalPerceptron
end
end
end

end OAI
