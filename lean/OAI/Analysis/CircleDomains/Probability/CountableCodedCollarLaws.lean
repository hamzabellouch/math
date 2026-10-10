import OAI.Analysis.CircleDomains.Probability.CountableCollarLaws

namespace OAI

/-! The common-collar argument with the varying base-code spaces retained.
Earlier-law constraints change those spaces during the transfinite recursion. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LinearOrder I] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem countable_of_uniformly_small_coded_collar_meetings
    (hcross : UnitDiskAlternatingContinua)
    (S : Set I) (V : Set X) (hV : IsOpen V) (f : X → ℂ)
    (hf : ContinuousOn f (closure V)) (hfinj : InjOn f (closure V))
    (hfdisk : MapsTo f (closure V) (Metric.closedBall 0 1))
    (χ : X → UnitAddCircle) (hχmeas : Measurable χ)
    (hχ : ∀ x ∈ frontier V, f x = standardCirclePoint (χ x))
    (Ω : I → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, ProbabilityMeasure (Ω i)) (a : ∀ i, Ω i → C(PathTime, X))
    (ha : ∀ i, Measurable (a i)) (p : I → X) (hp : ∀ i ∈ S, p i ∈ V)
    (hends : ∀ i ∈ S, ∀ᵐ z ∂(μ i : Measure (Ω i)), a i z ⊥ ∉ V ∧ a i z ⊤ = p i)
    (hatom : ∀ i ∈ S,
      NullSingletonClass (lastEntryCircleLaw ((μ i).map (a i)) V χ : Measure UnitAddCircle))
    (hsmall : ∀ i ∈ S, ∀ j ∈ S, i < j →
      4 * ((μ i : Measure (Ω i)).prod (μ j : Measure (Ω j)))
        {z | ∃ x ∈ V, x ∈ range (a i z.1) ∧ x ∈ range (a j z.2)} <
          (1 / 10 : ℝ≥0∞) ^ 4) : S.Countable := by
  by_contra hS
  obtain ⟨l, u, _, horder, hunc⟩ := exists_common_four_circle_arcs S hS
    (fun i => lastEntryCircleLaw ((μ i).map (a i)) V χ) hatom
  obtain ⟨i, hi, j, hj, hij⟩ := exists_lt_of_uncountable hunc
  have hm (i : I) (hi : i ∈ S ∧ ∀ k, (1 / 10 : ℝ≥0∞) <
      (lastEntryCircleLaw ((μ i).map (a i)) V χ : Measure UnitAddCircle)
        (rationalCircleArc (l k) (u k))) (k : Fin 4) :
      (1 / 10 : ℝ≥0∞) ≤ (μ i : Measure (Ω i))
        {z | χ (a i z (lastEntryTime (a i z) V)) ∈ rationalCircleArc (l k) (u k)} := by
    have h := (hi.2 k).le
    rw [lastEntryCircleLaw_apply _ V hV χ hχmeas] at h
    have hs : MeasurableSet {γ : C(PathTime, X) |
        χ (γ (lastEntryTime γ V)) ∈ rationalCircleArc (l k) (u k)} := by
      exact (hχmeas.comp (measurable_lastEntryLocation V hV))
        (measurableSet_rationalCircleArc _ _)
    rw [ProbabilityMeasure.map_apply' (μ i) (ha i).aemeasurable hs] at h
    exact h
  have hlow := collar_alternation_probability hcross V hV f hf hfinj hfdisk χ hχ
    (μ i) (μ j) (a i) (a j) (p i) (p j) (hp i hi.1) (hp j hj.1)
    (hends i hi.1) (hends j hj.1) l u horder (hm i hi 0) (hm i hi 2)
    (hm j hj 1) (hm j hj 3)
  exact (not_lt_of_ge hlow) (hsmall i hi.1 j hj.1 hij)

end CircleDomainRigidity

end

end OAI
