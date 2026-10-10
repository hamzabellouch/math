import Mathlib
import OAI.Combinatorics.SharpRamsey.Bounds.SamplingParameter
import OAI.Combinatorics.RamseyFive.Model

namespace OAI

open scoped BigOperators Classical
open Finset

namespace SharpRamseyFive

theorem ramseyProperty_eq_related (s t n : ℕ) :
    RamseyProperty s t n = SharpLogRamsey.RamseyProperty s t n := by
  unfold RamseyProperty SharpLogRamsey.RamseyProperty
  congr! 3
  funext B
  exact propext (SimpleGraph.isNClique_compl _).symm

theorem ramsey_eq_related (s t : ℕ) :
    ramsey s t = SharpLogRamsey.ramsey s t := by
  simp only [ramsey, SharpLogRamsey.ramsey, ramseyProperty_eq_related]

theorem upper_bound_eventually :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (ramsey 5 t : ℝ) ≤ C * (t : ℝ)^4 / (Real.log t)^3 := by
  simpa only [ramsey_eq_related, show 5-1 = 4 from rfl, show 5-2 = 3 from rfl]
    using SharpLogRamsey.Upper.ramsey_upper (s := 5) (by decide)

end SharpRamseyFive

end OAI
