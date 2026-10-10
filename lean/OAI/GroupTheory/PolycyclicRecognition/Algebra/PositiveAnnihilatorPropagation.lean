import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI

/-! # Propagating a positive annihilator relation

A relation expressing the identity as a finite sum of strictly positive
translates lets one push every translate into the nonnegative half-space.
This is the elementary algebraic step in the monoid-ring criterion for a
Bieri--Strebel direction.
-/

noncomputable section
namespace PolycyclicRecognition
variable {Q M : Type} [CommGroup Q] [AddCommGroup M]

theorem submodule_stable_of_positive_relation
    (ρ : Representation ℤ Q M) (χ : Q →* Multiplicative ℝ)
    (s : Finset Q) (c : Q → ℤ) {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ g ∈ s, δ ≤ (χ g).toAdd)
    (hrec : ∀ x : M, x = ∑ g ∈ s, c g • ρ g x)
    (U : Submodule ℤ M)
    (hU : ∀ q : Q, 0 ≤ (χ q).toAdd → ∀ x ∈ U, ρ q x ∈ U) :
    ∀ q : Q, ∀ x ∈ U, ρ q x ∈ U := by
  have hbound : ∀ n : ℕ, ∀ q : Q, -(n : ℝ) * δ ≤ (χ q).toAdd →
      ∀ x ∈ U, ρ q x ∈ U := by
    intro n
    induction n with
    | zero =>
      intro q hq x hx
      exact hU q (by simpa only [Nat.cast_zero, neg_zero, zero_mul] using hq) x hx
    | succ n ih =>
      intro q hq x hx
      rw [hrec (ρ q x)]
      apply U.sum_mem
      intro g hg
      apply U.smul_mem
      have hχ : (χ (g * q)).toAdd = (χ g).toAdd + (χ q).toAdd :=
        congrArg Multiplicative.toAdd (χ.map_mul g q)
      have hnext : -(n : ℝ) * δ ≤ (χ (g * q)).toAdd := by
        have hp := hs g hg
        rw [Nat.cast_succ] at hq
        rw [hχ]
        nlinarith
      have h := ih (g * q) hnext x hx
      simpa only [map_mul, Module.End.mul_apply] using h
  intro q x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (-(χ q).toAdd / δ)
  have hq : -(n : ℝ) * δ ≤ (χ q).toAdd := by
    have h := (div_lt_iff₀ hδ).mp hn
    linarith
  exact hbound n q hq x hx

end PolycyclicRecognition

end

end OAI
