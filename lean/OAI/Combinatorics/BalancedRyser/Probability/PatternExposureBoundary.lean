import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

theorem fixed_observable_eq (K : Finset P.Color) (x ω : P.Sample)
    (f : P.Sample → ℝ)
    (hf : ∀ y z, (∀ c ∈ K, y c = z c) → f y = f z) :
    f (P.fixCoordinates K x ω) = f x := by
  apply hf
  intro c hc
  simp [fixCoordinates, hc]

theorem fixedExpectation_eq_of_dependsOn (K : Finset P.Color) (x : P.Sample)
    (f : P.Sample → ℝ)
    (hf : ∀ y z, (∀ c ∈ K, y c = z c) → f y = f z) :
    P.fixedExpectation K x f = f x := by
  unfold fixedExpectation
  simp_rw [P.fixed_observable_eq K x _ f hf]
  simp

theorem indicator_fixed_eq_of_support_subset (K : Finset P.Color)
    (x ω : P.Sample) (a : P.Label) (ha : P.support a ⊆ K) :
    P.indicator a (P.fixCoordinates K x ω) = P.indicator a x := by
  apply P.indicator_eq_of_agree
  intro c hc
  simp [fixCoordinates, ha hc]

theorem fixedExpectation_indicator_of_support_subset (K : Finset P.Color)
    (x : P.Sample) (a : P.Label) (ha : P.support a ⊆ K) :
    P.fixedExpectation K x (P.indicator a) = P.indicator a x := by
  apply P.fixedExpectation_eq_of_dependsOn
  intro y z hyz
  exact P.indicator_eq_of_agree a y z (fun c hc => hyz c (ha hc))

theorem count_fixed_eq_of_supports_subset (K : Finset P.Color)
    (x ω : P.Sample) (hK : ∀ a, P.support a ⊆ K) :
    P.count (P.fixCoordinates K x ω) = P.count x := by
  classical
  unfold count
  apply Finset.sum_congr rfl
  intro a _
  exact P.indicator_fixed_eq_of_support_subset K x ω a (hK a)

theorem fixedExpectation_count_comp_of_supports_subset (K : Finset P.Color)
    (x : P.Sample) (hK : ∀ a, P.support a ⊆ K) (f : ℝ → ℝ) :
    P.fixedExpectation K x (fun ω => f (P.count ω)) = f (P.count x) := by
  unfold fixedExpectation
  simp_rw [P.count_fixed_eq_of_supports_subset K x _ hK]
  simp

theorem fixedExpectation_count_of_supports_subset (K : Finset P.Color)
    (x : P.Sample) (hK : ∀ a, P.support a ⊆ K) :
    P.fixedExpectation K x P.count = P.count x :=
  P.fixedExpectation_count_comp_of_supports_subset K x hK id

theorem centered_moment_eq_zero_of_supports_subset (K : Finset P.Color)
    (x : P.Sample) (hK : ∀ a, P.support a ⊆ K) {n : ℕ} (hn : 0 < n) :
    P.fixedExpectation K x (fun ω =>
      |P.count ω - P.fixedExpectation K x P.count| ^ n) = 0 := by
  rw [P.fixedExpectation_count_of_supports_subset K x hK]
  rw [P.fixedExpectation_count_comp_of_supports_subset K x hK
    (fun z => |z - P.count x| ^ n)]
  simp [Nat.ne_of_gt hn]

theorem overlapCount_eq_zero_of_supports_subset (K₀ K : Finset P.Color)
    (hK : ∀ a, P.support a ⊆ K₀) (ω : P.Sample) :
    P.overlapCount K₀ K ω = 0 := by
  classical
  unfold overlapCount
  apply Finset.sum_eq_zero
  intro a _
  simp [Finset.sdiff_eq_empty_iff_subset.mpr (hK a)]

@[simp] theorem count_eq_zero_of_isEmpty [IsEmpty P.Label] (ω : P.Sample) :
    P.count ω = 0 := by
  simp [count]

end Balanced.PatternModel

end OAI
