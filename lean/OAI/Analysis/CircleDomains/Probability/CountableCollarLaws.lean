import OAI.Analysis.CircleDomains.Probability.CollarAlternationProbability
import OAI.Analysis.CircleDomains.Probability.LastEntryCircleLaw
import OAI.Analysis.CircleDomains.Selection.UncountableChoice

namespace OAI

/-! The common-collar contradiction for a linearly ordered family of actual
path laws. The hypotheses retain the original quantitative meeting estimate. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LinearOrder I]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] in
theorem countable_of_uniformly_small_collar_meetings
    (hcross : UnitDiskAlternatingContinua)
    (S : Set I) (V : Set X) (hV : IsOpen V) (f : X → ℂ)
    (hf : ContinuousOn f (closure V)) (hfinj : InjOn f (closure V))
    (hfdisk : MapsTo f (closure V) (Metric.closedBall 0 1))
    (χ : X → UnitAddCircle) (hχmeas : Measurable χ)
    (hχ : ∀ x ∈ frontier V, f x = standardCirclePoint (χ x))
    (μ : I → ProbabilityMeasure C(PathTime, X)) (p : I → X)
    (hp : ∀ i ∈ S, p i ∈ V)
    (hends : ∀ i ∈ S, ∀ᵐ γ ∂(μ i : Measure C(PathTime, X)),
      γ ⊥ ∉ V ∧ γ ⊤ = p i)
    (hatom : ∀ i ∈ S,
      NullSingletonClass (lastEntryCircleLaw (μ i) V χ : Measure UnitAddCircle))
    (hsmall : ∀ i ∈ S, ∀ j ∈ S, i < j →
      4 * ((μ i : Measure C(PathTime, X)).prod (μ j : Measure C(PathTime, X)))
        {z | ∃ x ∈ V, x ∈ range z.1 ∧ x ∈ range z.2} < (1 / 10 : ℝ≥0∞) ^ 4) :
    S.Countable := by
  by_contra hS
  obtain ⟨l, u, _, horder, hunc⟩ := exists_common_four_circle_arcs S hS
    (fun i => lastEntryCircleLaw (μ i) V χ) hatom
  obtain ⟨i, hi, j, hj, hij⟩ := exists_lt_of_uncountable hunc
  have hm (i : I) (hi : i ∈ S ∧ ∀ k, (1 / 10 : ℝ≥0∞) <
      (lastEntryCircleLaw (μ i) V χ : Measure UnitAddCircle)
        (rationalCircleArc (l k) (u k))) (k : Fin 4) :
      (1 / 10 : ℝ≥0∞) ≤ (μ i : Measure C(PathTime, X))
        {γ | χ (γ (lastEntryTime γ V)) ∈ rationalCircleArc (l k) (u k)} := by
    rw [← lastEntryCircleLaw_apply (μ i) V hV χ hχmeas]
    exact (hi.2 k).le
  have hlow := collar_alternation_probability hcross V hV f hf hfinj hfdisk χ hχ
    (μ i) (μ j) id id (p i) (p j) (hp i hi.1) (hp j hj.1)
    (hends i hi.1) (hends j hj.1) l u horder (hm i hi 0) (hm i hi 2)
    (hm j hj 1) (hm j hj 3)
  exact (not_lt_of_ge hlow) (hsmall i hi.1 j hj.1 hij)

end CircleDomainRigidity

end

end OAI
