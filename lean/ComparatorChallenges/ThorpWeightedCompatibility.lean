import Mathlib

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

abbrev Rows (A D : ℕ) := Fin A → Equiv.Perm (Fin D)
abbrev Cols (A D : ℕ) := Fin D → Equiv.Perm (Fin A)

def Compatible {A D : ℕ} (r : Rows A D) (c : Cols A D) : Prop :=
  ∀ j : Fin D, Function.Injective (fun i : Fin A => c (r i j) i)

noncomputable def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

noncomputable def marginalFactor {α : Type*} [Fintype α]
    (θ : ℝ) (w : α → ℝ) : ℝ :=
  (uniformMean (fun x => Real.rpow (w x) (1 / θ))) ^ θ

noncomputable def weightedCompatibility (A D : ℕ)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ) : ℝ := by
  classical
  exact (Nat.factorial (A * D) : ℝ) /
    ((Nat.factorial D : ℝ) ^ A * (Nat.factorial A : ℝ) ^ D) *
    uniformMean (fun rc : Rows A D × Cols A D =>
      if Compatible rc.1 rc.2 then (∏ i, w i (rc.1 i)) * (∏ k, v k (rc.2 k)) else 0)

def WeightedCompatibilityTheorem : Prop :=
  ∃ L C₀ m₀ : ℝ, 0 < L ∧ 0 < C₀ ∧ 0 < m₀ ∧
    ∀ A D : ℕ,
    let n : ℝ := A * D
    let m := Real.sqrt n
    let θ := 1 - L / Real.log m
    m₀ ≤ m → 0 < θ → m / ((2 : ℕ) : ℝ) ≤ A → (A : ℝ) ≤ ((2 : ℕ) : ℝ) * m →
    m / ((2 : ℕ) : ℝ) ≤ D → (D : ℝ) ≤ ((2 : ℕ) : ℝ) * m →
    ∀ (w : Fin A → Equiv.Perm (Fin D) → ℝ)
      (v : Fin D → Equiv.Perm (Fin A) → ℝ),
    (∀ i σ, 0 ≤ w i σ) → (∀ k σ, 0 ≤ v k σ) →
    weightedCompatibility A D w v ≤
      Real.exp (C₀ * n ^ (((54 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))) *
        (∏ i, marginalFactor θ (w i)) * (∏ k, marginalFactor θ (v k))


theorem weightedCompatibility_main : WeightedCompatibilityTheorem := by
  sorry

end ThorpCompatibility

end OAI
