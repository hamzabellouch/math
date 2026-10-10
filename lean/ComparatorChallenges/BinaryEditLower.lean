import Mathlib

namespace OAI

namespace TreeEdit

universe u

/-- A single unit-cost insertion, deletion, or substitution at any position. -/
inductive EditStep {α : Type u} : List α → List α → Prop
  | insert (p q : List α) (a : α) : EditStep (p ++ q) (p ++ a :: q)
  | delete (p q : List α) (a : α) : EditStep (p ++ a :: q) (p ++ q)
  | substitute (p q : List α) (a b : α) : EditStep (p ++ a :: q) (p ++ b :: q)

/-- An edit script with no restriction on intermediate word lengths. -/
inductive EditScript {α : Type u} : List α → List α → ℕ → Prop
  | nil (x : List α) : EditScript x x 0
  | cons {x y z : List α} {n : ℕ} :
      EditStep x y → EditScript y z n → EditScript x z (n + 1)

noncomputable def ed {α : Type u} (x y : List α) : ℕ :=
  sInf {n | EditScript x y n}

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1
abbrev Word (α : Type u) (n : ℕ) := {x : List α // x.length = n}

namespace BinaryLower

/-- The product of the two maximal pairwise distance ratios. -/
noncomputable def distortion {X : Type u} (ρ : X → X → ℝ) (f : X → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} *
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

/-- The infimum over every injective map into the full real sequence space ℓ₁. -/
noncomputable def c1 (X : Type u) (ρ : X → X → ℝ) : ℝ :=
  sInf {D : ℝ | ∃ f : X → RealL1, Function.Injective f ∧ D = distortion ρ f}

noncomputable def binarySetDistortion {n : ℕ} (W : Finset (Word Bool n)) : ℝ :=
  c1 {x : Word Bool n // x ∈ W}
    (fun x y => (ed x.val.val y.val.val : ℝ))

noncomputable def growth (c : ℝ) (d : ℕ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))))

end BinaryLower

open BinaryLower

/-- The binary lower-bound theorem of OpenAI's September 27, 2026 tree-constructions
manuscript: finite equal-length witnesses for every sufficiently large length cap. -/
theorem binary_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  sorry

end TreeEdit

end OAI
