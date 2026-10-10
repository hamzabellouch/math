import Mathlib

namespace OAI

namespace TreeEdit

universe u

/-- A single unit-cost insertion, deletion or substitution, at any position. -/
inductive EditStep {α : Type u} : List α → List α → Prop
  | insert (p q : List α) (a : α) : EditStep (p ++ q) (p ++ a :: q)
  | delete (p q : List α) (a : α) : EditStep (p ++ a :: q) (p ++ q)
  | substitute (p q : List α) (a b : α) : EditStep (p ++ a :: q) (p ++ b :: q)

/-- A script of precisely `n` edits. There is no restriction on its intermediate lengths. -/
inductive EditScript {α : Type u} : List α → List α → ℕ → Prop
  | nil (x : List α) : EditScript x x 0
  | cons {x y z : List α} {n : ℕ} :
      EditStep x y → EditScript y z n → EditScript x z (n + 1)

/-- Ordinary unit-cost edit distance. The set is nonempty (delete then insert). -/
noncomputable def ed {α : Type u} (x y : List α) : ℕ :=
  sInf {n | EditScript x y n}

/-- The full infinite-dimensional real ℓ₁ space. -/
abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

/-- Product of the two maximal pairwise distance ratios. -/
noncomputable def distortion (W : Finset (List Bool)) (f : W → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧
      r = dist (f x) (f y) / (ed x.val y.val : ℝ)} *
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧
      r = (ed x.val y.val : ℝ) / dist (f x) (f y)}

/-- Infimum over all injective ℓ₁ maps, used on finite sets with at least two points. -/
noncomputable def c1 (W : Finset (List Bool)) : ℝ :=
  sInf {D : ℝ | ∃ f : W → RealL1, Function.Injective f ∧ distortion W f = D}

/-- The binary main endpoint, for every sufficiently large cap (natural logarithms). -/
def BinaryLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∃ n : ℕ, n ≤ d ∧ ∃ W : Finset (List Bool),
      2 ≤ W.card ∧ (∀ w ∈ W, w.length = n) ∧
      Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤ c1 W

theorem binary_torus : BinaryLowerBound := by
  sorry

end TreeEdit

end OAI
