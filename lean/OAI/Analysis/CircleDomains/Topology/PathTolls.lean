import OAI.Analysis.CircleDomains.Selection.VisitCardinality
import OAI.Analysis.CircleDomains.Selection.MeanVisits

namespace OAI

/-! Boundary tolls count every parameter visit. Counting-square-summable
weights have countable support, so their true tolls are Borel. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def boundaryToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t : PathTime, m (γ t)

theorem boundaryToll_eq_visits (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = ∑' x, m x * visitCount γ x := by
  rw [boundaryToll, ← ENNReal.tsum_fiberwise (fun t => m (γ t)) γ]
  apply tsum_congr
  intro x
  rw [visitCount_eq_tsum, ← ENNReal.tsum_mul_left,
    tsum_subtype (γ ⁻¹' {x}) (fun t : PathTime => m (γ t))]
  apply tsum_congr
  intro t
  by_cases h : γ t = x
  · simp [h, Set.indicator]
  · simp [h, Set.indicator]

theorem boundaryToll_eq_support (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = ∑' x : Function.support m, m x * visitCount γ x := by
  rw [boundaryToll_eq_visits]
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun x : X => m x * visitCount γ x)
  intro x hx
  contrapose! hx
  simp only [Function.mem_support] at hx ⊢
  simp [hx]

omit [MetricSpace X] in
theorem countable_support_of_summable_sq {m : X → ℝ}
    (hm : Summable (fun x => (m x) ^ 2)) :
    (Function.support (fun x => ENNReal.ofReal (m x))).Countable := by
  apply hm.countable_support.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  exact pow_ne_zero _ (fun h => hx (by simp [h]))

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_boundaryToll {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    Measurable (fun γ : C(PathTime, X) => boundaryToll γ m) := by
  let : Countable (Function.support m) := hm.to_subtype
  simp_rw [boundaryToll_eq_support]
  exact Measurable.tsum fun x => measurable_const.mul
    (measurable_visitCount.comp (measurable_id.prodMk measurable_const))

theorem measurable_boundaryToll_of_summable_sq {m : X → ℝ}
    (hm : Summable (fun x => (m x) ^ 2)) :
    Measurable (fun γ : C(PathTime, X) => boundaryToll γ (fun x => ENNReal.ofReal (m x))) :=
  measurable_boundaryToll (countable_support_of_summable_sq hm)

theorem lintegral_boundaryToll (μ : ProbabilityMeasure C(PathTime, X))
    {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    ∫⁻ γ, boundaryToll γ m ∂(μ : Measure _) =
      ∑' x : Function.support m, m x * meanVisitCount μ x := by
  let : Countable (Function.support m) := hm.to_subtype
  simp_rw [boundaryToll_eq_support]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro x
    exact lintegral_const_mul _
      (measurable_visitCount.comp (measurable_id.prodMk measurable_const))
  · intro x
    exact (measurable_const.mul
      (measurable_visitCount.comp (measurable_id.prodMk measurable_const))).aemeasurable

end CircleDomainRigidity

end

end OAI
