import Mathlib.Logic.Equiv.Prod
import OAI.Computability.UniqueGames.PCP.AssignmentTester

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Hastad

variable {V D : Type*}

/-- The common fiber left after separating a Boolean character's sign. -/
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

section Walsh

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

/-- Actual parity words from independently indexed uniform cube vectors have
exactly the uniform Boolean-word distribution. -/
theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

/-- The same joint law expressed with the actual real Walsh character values. -/
theorem expect_walsh_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → ℝ) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => walsh s (g d))) =
      𝔼 b : D → Bool, F (fun d => bitSign (b d)) := by
  simpa only [AssignmentTester.bitSign_parity] using
    expect_parity_samples s hs (fun b => F (fun d => bitSign (b d)))

/-- In particular, any test of the empirical Walsh bias has the corresponding
uniform Boolean-word average. This is the eigenvalue sampling law. -/
theorem expect_walsh_mean (s : Cube I) (hs : s ≠ fun _ => false) (F : ℝ → ℝ) :
    (𝔼 g : D → Cube I, F (𝔼 d, walsh s (g d))) =
      𝔼 b : D → Bool, F (𝔼 d, bitSign (b d)) :=
  expect_walsh_samples s hs (fun z => F (𝔼 d, z d))

end Walsh

end UniqueGamesTheorem.Foundations.PCP.CayleySampling

end

end

end OAI
