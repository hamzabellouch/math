import Mathlib
import OAI.Combinatorics.SharpRamsey.Bounds.SamplingParameter
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.SharpRamsey.Geometry.Weight
import OAI.Combinatorics.RamseyFive.Entropy.FinalValidationBudget
import OAI.Combinatorics.RamseyFive.Iteration.EventuallyRichScale
import OAI.Combinatorics.RamseyFive.Entropy.RetainedCounters
import OAI.Combinatorics.RamseyFive.Entropy.TreeOmissionBound
import OAI.Combinatorics.RamseyFive.Entropy.RevealMarginalDeficit
import OAI.Combinatorics.RamseyFive.Geometry.LowConflictSubsets
import OAI.Combinatorics.RamseyFive.Bounds.PrimeStream

namespace OAI

namespace SharpRamseyFive
open Filter

theorem sharpBounds : SharpBounds := by
  obtain ⟨C, hC, n₀, hupper⟩ := upper_bound_eventually
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have hlo := lower_arbitrary_slack (fun η hη hη' => primeConstruction hη hη') hε
  obtain ⟨m₀, hlower⟩ := eventually_atTop.mp hlo
  exact ⟨max n₀ m₀, fun t ht =>
    ⟨hlower t ((le_max_right _ _).trans ht), hupper t ((le_max_left _ _).trans ht)⟩⟩

theorem main : SharpBounds ∧ SharpExponent :=
  ⟨sharpBounds, sharpExponent_of_sharpBounds sharpBounds⟩
end SharpRamseyFive

end OAI
