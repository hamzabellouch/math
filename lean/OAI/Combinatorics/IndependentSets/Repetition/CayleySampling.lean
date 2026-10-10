import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Bits

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem card_boolean_split [Fintype V] (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    Fintype.card V = 2 * Fintype.card (FalseFiber χ) := by
  simpa using Fintype.card_congr (booleanSplitEquiv χ flip hflip hχ)

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

end IndependentSetsGames.Foundations.PCP.CayleySampling
end

end OAI
