import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.Stability

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem corePencilEvent_of_not_nearCoverFailure
    (hstable : PrimeStability.{u}) (hprime : Nat.Prime (Fintype.card F))
    {ζ : ℝ} (hζ : 0 < ζ)
    (hlarge : max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ))
    {D : Finset (Line F)}
    (hnear : ¬ NearCoverFailure (stabilityDensity ζ) D) :
    CorePencilEvent ζ D := by
  intro C hdisj hcard hcover
  apply hstable F hprime ζ hζ hlarge C hcard
  by_contra h
  exact hnear ⟨C, hdisj, hcard, hcover, le_of_not_gt h⟩

theorem corePencilFailure_subset_nearCoverFailure
    (hstable : PrimeStability.{u}) (hprime : Nat.Prime (Fintype.card F))
    {ζ : ℝ} (hζ : 0 < ζ)
    (hlarge : max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ)) :
    {D : Finset (Line F) | ¬ CorePencilEvent ζ D} ⊆
      {D | NearCoverFailure (stabilityDensity ζ) D} := by
  intro D hD
  by_contra hnear
  exact hD (corePencilEvent_of_not_nearCoverFailure hstable hprime hζ hlarge hnear)

end Balanced

end OAI
