import OAI.Probability.SpanningForest.FinitePosteriorTilt

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336.FinitePosterior

theorem brownian_finset_endpoint_law
    {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (S : Finset I) (t : ℝ≥0) :
    P.map (fun ω (i : S) => C i t ω) =
      Measure.pi (fun _ : S => gaussianReal 0 t) := by
  classical
  have hi : iIndepFun (fun (i : S) ω => C i t ω) P :=
    (hind.precomp Subtype.val_injective).comp
      (fun _ f => f t) (fun _ => measurable_pi_apply t)
  rw [hi.map_fun_eq_pi_map (fun (i : S) => (hC i).aemeasurable t)]
  congr 1
  funext i
  exact ((hC i).hasLaw_eval t).map_eq

theorem brownian_binaryField_finset_condExp
    {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ProbabilityMeasure (I → Bool))
    (X : Ω → (I → Bool)) (hX : Measurable X)
    (hprior : P.map X = (ν : Measure (I → Bool)))
    (C : I → ℝ≥0 → Ω → ℝ) (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (hCm : ∀ i s, Measurable (C i s))
    (hXC : X ⟂ᵢ[P] (fun ω (p : I × ℝ≥0) => C p.1 p.2 ω))
    (S : Finset I) (e : I) (t : ℝ≥0) (ht : t ≠ 0) :
    let Y := fun ω i => (t : ℝ) * TiltLimit.bit (X ω i) + C i t ω
    P[fun ω => TiltLimit.bit (X ω e) |
      (inferInstance : MeasurableSpace (S → ℝ)).comap (fun ω (i : S) => Y ω i)] =ᵐ[P]
      fun ω => TiltLimit.finiteTiltMean ν S (fun i => Y ω i - (t : ℝ) / 2) e := by
  have hnoise : Measurable (fun ω i => C i t ω) :=
    Measurable.of_eval (fun i => hCm i t)
  have hi : X ⟂ᵢ[P] (fun ω i => C i t ω) := by
    exact hXC.comp measurable_id
      (show Measurable (fun f : I × ℝ≥0 → ℝ => fun i => f (i, t)) from
        Measurable.of_eval (fun i => measurable_pi_apply (i, t)))
  exact binaryField_finset_condExp P ν X (fun ω i => C i t ω)
    hX hnoise S e t ht hprior (brownian_finset_endpoint_law hC hind S t) hi

end Problem336.FinitePosterior

end

end OAI
