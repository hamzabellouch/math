import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.RestrictionLawBad

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Filter
open scoped Topology

theorem no_uniformly_bad_finite_patterns {s d : ℕ} {ξ : ℝ} (hξ : 0 < ξ)
    (hcounter : ∀ r, s ≤ r → ∃ μ : ProbabilityMeasure (ListPattern s d (Fin r)),
      ∀ e : Fin s ↪o Fin r,
        ξ ≤ (μ {C | ¬GoodPatternOn (C.restrict e) Finset.univ} : ℝ)) : False := by
  classical
  have hex (k : ℕ) := homogeneous_bad_finite_law hcounter k
    (1 / ((k : ℝ) + 1)) (by positivity)
  choose μ hhom hbad using hex
  let seq (k : ℕ) := extensionLaw (rationalExhaustion k) (rationalExhaustion_card k) (μ k)
  let natRat : ℕ ↪o ℚ := ⟨⟨Nat.cast, Nat.cast_injective⟩, by simp⟩
  let e₀ : Fin s ↪o ℚ := (Fin.valOrderEmb s).trans natRat
  apply no_asymptotically_invariant_bad_sequence hξ seq _ e₀
  · filter_upwards [eventually_range_rationalExhaustion e₀] with k hk
    rw [← restrictionLaw_bad]
    change ξ ≤ ((restrictionLaw e₀ (extensionLaw (rationalExhaustion k)
      (rationalExhaustion_card k) (μ k))) {D | ¬GoodPatternOn D Finset.univ} : ℝ)
    rw [restriction_extensionLaw_inside _ _ _ hk, restrictionLaw_bad]
    exact hbad k _
  · intro n e f
    filter_upwards [eventually_ge_atTop n,
      eventually_range_rationalExhaustion e, eventually_range_rationalExhaustion f]
      with k hnk he hf
    change dist (restrictionLaw e (extensionLaw (rationalExhaustion k) _ (μ k)))
      (restrictionLaw f (extensionLaw (rationalExhaustion k) _ (μ k))) ≤ _
    rw [restriction_extensionLaw_inside _ _ _ he, restriction_extensionLaw_inside _ _ _ hf]
    exact (hhom k n hnk _ _).le

end LargeIndependentSets

end OAI
