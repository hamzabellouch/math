import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Basic.Real.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def uncoveredPoints (C : Finset (Line F)) : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C, ¬ OnLine p l)

def pencilSize (C : Finset (Line F)) (P : ProjectivePoint F) : ℕ :=
  (C.filter (fun l => ThroughProjective l P)).card

noncomputable def stabilityDensity (ζ : ℝ) : ℝ := min (ζ / 4) (1 / 100)

def PrimeStability : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
    Nat.Prime (Fintype.card F) →
    ∀ ζ : ℝ, 0 < ζ →
      max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ) →
      ∀ C : Finset (Line F), C.card ≤ Fintype.card F →
        (uncoveredPoints C).card < stabilityDensity ζ * (Fintype.card F : ℝ) ^ 2 →
        ∃ P : ProjectivePoint F,
          (1 - ζ) * (Fintype.card F : ℝ) ≤ (pencilSize C P : ℝ)

def CorePencilEvent (ζ : ℝ) (D : Finset (Line F)) : Prop :=
  ∀ C : Finset (Line F), Disjoint C D → C.card ≤ Fintype.card F →
    CoversPoints C (uncoveredPoints D) →
    ∃ P : ProjectivePoint F,
      (1 - ζ) * (Fintype.card F : ℝ) ≤ (pencilSize C P : ℝ)

def NearCoverFailure (δ : ℝ) (D : Finset (Line F)) : Prop :=
  ∃ C : Finset (Line F), Disjoint C D ∧ C.card ≤ Fintype.card F ∧
    CoversPoints C (uncoveredPoints D) ∧
    δ * (Fintype.card F : ℝ) ^ 2 ≤ ((uncoveredPoints C).card : ℝ)

end Balanced

end OAI
