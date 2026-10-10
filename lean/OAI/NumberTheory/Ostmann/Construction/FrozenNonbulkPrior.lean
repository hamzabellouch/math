import OAI.NumberTheory.Ostmann.Construction.FiniteCoordinatePrior
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCoordinateInsertion

namespace OAI

/-! # Freeze nonbulk data while resampling the original product law -/

namespace Ostmann
open scoped Classical BigOperators

theorem finiteCoordinatePriors_frozen {σ A : Type*} [Fintype A]
    (μ : σ → A → ℝ) (order : List σ) (F : (σ → A) → (σ → A) → ℂ)
    (hfrozen : ∀ i ∈ order, ∀ x a y, F (Function.update x i a) y = F x y)
    (x : σ → A) :
    finiteCoordinatePriors μ order (fun y => F y y) x =
      finiteCoordinatePriors μ order (F x) x := by
  induction order generalizing x with
  | nil => rfl
  | cons i order ih =>
    change (∑ a, (μ i a : ℂ) * finiteCoordinatePriors μ order (fun y => F y y)
      (Function.update x i a)) = _
    change _ = ∑ a, (μ i a : ℂ) * finiteCoordinatePriors μ order (F x) (Function.update x i a)
    apply Finset.sum_congr rfl
    intro a _
    rw [ih (fun j hj => hfrozen j (by simp [hj]))]
    have he : F (Function.update x i a) = F x := funext (hfrozen i (by simp) x a)
    rw [he]

theorem finite_prior_frozen_mean {σ A : Type*} [Fintype σ] [Fintype A]
    (μ : σ → A → ℝ) (hmass : ∀ i, ∑ a, μ i a = 1)
    (order : List σ) (F : (σ → A) → (σ → A) → ℂ)
    (hfrozen : ∀ i ∈ order, ∀ x a y, F (Function.update x i a) y = F x y) :
    (∑ x, ((∏ i, μ i (x i) : ℝ) : ℂ) * finiteCoordinatePriors μ order (F x) x) =
      ∑ x, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x x := by
  simp_rw [← finiteCoordinatePriors_frozen μ order F hfrozen]
  exact finiteCoordinatePriors_preserves μ hmass order (fun x => F x x)

theorem bulkCoordinateInsert_update_base {σ J : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (y : J → ℝ) (j : J) (a : ℝ) :
    bulkCoordinateInsert (Function.update base (e j) a) e y = bulkCoordinateInsert base e y := by
  funext i
  by_cases hi : ∃ k, e k = i
  · simp only [bulkCoordinateInsert, dite_eq_left hi]
  · simp only [bulkCoordinateInsert, dite_eq_right hi]
    exact Function.update_of_ne (fun h => hi ⟨j, h.symm⟩) a base

end Ostmann

end OAI
