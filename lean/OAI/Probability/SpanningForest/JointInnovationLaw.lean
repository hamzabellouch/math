import OAI.Probability.SpanningForest.InnovationIdentification
import OAI.Probability.SpanningForest.JointProcessLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336.JointInnovationLaw

variable {Ω Ω' I : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]

omit [IsProbabilityMeasure Q] in

theorem identDistrib_of_past_characteristic
    (F : Filtration ℝ≥0 mΩ)
    (W : I → ℝ≥0 → Ω → ℝ) (B : I → ℝ≥0 → Ω' → ℝ)
    (hW : ∀ i, Adapted F (W i)) (hB : ∀ i t, Measurable (B i t))
    (hW0 : ∀ i, ∀ᵐ ω ∂P, W i 0 ω = 0)
    (hB0 : ∀ i, ∀ᵐ ω ∂Q, B i 0 ω = 0)
    (ν : (S : Finset I) → ℝ≥0 → ℝ≥0 → Measure (EuclideanSpace ℝ S))
    [∀ S s t, IsProbabilityMeasure (ν S s t)]
    (hchar : ∀ (S : Finset I) (s t : ℝ≥0), s ≤ t →
      ∀ A : Set Ω, MeasurableSet[F s] A → ∀ θ : EuclideanSpace ℝ S,
      (∫ ω in A, Complex.exp ((inner ℝ
        (WithLp.toLp 2 (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S) θ : ℂ)
          * Complex.I) ∂P) = (P A).toReal • charFun (ν S s t) θ)
    (hBi : ∀ S : Finset I, HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) Q)
    (hBLaw : ∀ (S : Finset I) (s t : ℝ≥0), s ≤ t →
      HasLaw (fun ω => (WithLp.toLp 2 (fun i : S => B i t ω - B i s ω) :
        EuclideanSpace ℝ S)) (ν S s t) Q) :
    IdentDistrib (fun ω i t => W i t ω) (fun ω i t => B i t ω) P Q := by
  have hWS (S : Finset I) : Adapted F
      (fun t ω => (WithLp.toLp 2 (fun i : S => W i t ω) : EuclideanSpace ℝ S)) := by
    intro t
    let : MeasurableSpace Ω := F t
    exact (MeasurableEquiv.toLp 2 (S → ℝ)).measurable.comp
      (Measurable.of_eval (fun i => hW i t))
  refine JointProcessLaw.identDistrib_family_of_finite_increments
    (fun i t => (hW i).measurable (i := t)) hB hW0 hB0 ?_ hBi ?_
  · intro S
    exact InnovationIdentification.hasIndepIncrements_of_past_characteristic
      (hWS S) (hchar S)
  · intro S s t hst
    have hD : Measurable (fun ω => (WithLp.toLp 2
        (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S)) :=
      ((hWS S).measurable (i := t)).sub ((hWS S).measurable (i := s))
    have hlaw : HasLaw (fun ω => (WithLp.toLp 2
        (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S)) (ν S s t) P := by
      refine ⟨hD.aemeasurable, ?_⟩
      have h := InnovationIdentification.restrict_map_eq_smul_of_characteristic
        hD Set.univ (hchar S s t hst Set.univ MeasurableSet.univ)
      simpa using h
    exact hlaw.identDistrib (hBLaw S s t hst)

end Problem336.JointInnovationLaw

end

end OAI
