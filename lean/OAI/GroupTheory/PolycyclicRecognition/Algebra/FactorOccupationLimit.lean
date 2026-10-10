import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationWeakLimit

namespace OAI

/-! # Combining the two actual factor estimates for occupation limits -/

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology

/-- Separate right-translation estimates in the two factors suffice for
full invariance. Factorizations may be nonunique. -/
theorem invariant_of_weak_factor_occupation_limit
    {G X ι : Type*} [Group G] [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MulAction G X] [ContinuousConstSMul G X]
    (N D : Subgroup G)
    (hgen : ∀ g : G, ∃ n : N, ∃ d : D, g = (n : G) * d)
    {l : Filter ι} [l.NeBot]
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs l (𝓝 μ))
    (hN : ∀ (n : N) (f : C(X, ℝ)), Tendsto
      (fun i => (∫ x, f ((n : G) • x) ∂(μs i : Measure X)) -
        ∫ x, f x ∂(μs i : Measure X)) l (𝓝 0))
    (hD : ∀ (d : D) (f : C(X, ℝ)), Tendsto
      (fun i => (∫ x, f ((d : G) • x) ∂(μs i : Measure X)) -
        ∫ x, f x ∂(μs i : Measure X)) l (𝓝 0)) :
    SMulInvariantMeasure G X (μ : Measure X) := by
  apply invariant_of_weak_occupation_limit μs μ hlim
  intro g f
  obtain ⟨n, d, rfl⟩ := hgen g
  let fn : C(X, ℝ) :=
    ⟨fun x => f ((n : G) • x), f.continuous.comp (continuous_const_smul _)⟩
  have ht := (hD d fn).add (hN n f)
  simp only [add_zero] at ht
  apply ht.congr
  intro i
  simp only [fn, ContinuousMap.coe_mk, ← mul_smul]
  ring

end PolycyclicRecognition

end OAI
