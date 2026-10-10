import Mathlib
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditDistortion

universe u

/- A single unit-cost insertion, deletion, or (when enabled) substitution. -/


/- An unrestricted script of exactly n unit edits. -/


/-- Minimum script length. Scripts always exist (delete x and insert y). -/


abbrev L1 := lp (fun _ : ℕ => ℝ) 1

/-- The product of the two maximal distance ratios. -/
noncomputable def distortion {X : Type u} (ρ : X → X → ℝ) (f : X ↪ L1) : ℝ :=
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} *
    sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

/-- The infimum over injective maps to real absolutely summable sequences. -/
noncomputable def leastDistortion {X : Type u} (ρ : X → X → ℝ) : ℝ :=
  sInf (Set.range (distortion ρ))

abbrev Words (Alpha : Type u) (d : ℕ) := {x : List Alpha // x.length ≤ d}

noncomputable def E (Alpha : Type u) (d : ℕ) : ℝ :=
  leastDistortion (fun x y : Words Alpha d => (edit x.val y.val : ℝ))

noncomputable def exponentScale (c : ℝ) (d : ℕ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))))

/-- Supremum over finite alphabet cardinalities. -/
noncomputable def alphabetSup (d : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d}

/-- A finite nonempty subset of binary words of one common length. -/
def BinaryWitness (c : ℝ) (d : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧ ∃ S : Set (List Bool), S.Finite ∧ S.Nonempty ∧
    (∀ w ∈ S, w.length = n) ∧
    exponentScale c d ≤ leastDistortion (fun x y : S => (edit x.val y.val : ℝ))

/-- Uniform two-sided bounds with common positive constants and threshold. -/
def MainClaim : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ (Alpha : Type u) [Fintype Alpha], 2 ≤ Fintype.card Alpha →
      exponentScale c d ≤ E Alpha d ∧ E Alpha d ≤ exponentScale C d) ∧
    BinaryWitness c d ∧
    exponentScale c d ≤ alphabetSup d ∧ alphabetSup d ≤ exponentScale C d

end EditDistortion

end OAI
