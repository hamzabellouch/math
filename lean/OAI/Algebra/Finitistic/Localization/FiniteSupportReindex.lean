import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.LinearAlgebra.Pi

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.FiniteSupportReindex
universe u
variable {R : Type u} [Ring R]
variable (V : ℤ → ModuleCat.{u} R)
variable {l m : ℕ} (p : Fin l → ℤ) (q : Fin m → ℤ)

/-- Extend a finite family of actual components by zero in every other degree. -/
def coefficient (n : ℤ) : (∀ i, V (p i)) →ₗ[R] V n := by
  classical
  exact if h : ∃ i, p i = n then
    ((eqToHom (congrArg V h.choose_spec)).hom).comp (LinearMap.proj h.choose)
  else 0

@[simp] theorem coefficient_at (hp : Function.Injective p) (i : Fin l) (x : ∀ i, V (p i)) :
    coefficient V p (p i) x = x i := by
  classical
  unfold coefficient
  split_ifs with h
  · have transport (j : Fin l) (hji : j=i) (hpi : p j=p i) :
        (eqToHom (congrArg V hpi)).hom (x j) = x i := by
      subst j
      rfl
    exact transport h.choose (hp h.choose_spec) h.choose_spec
  · exact False.elim (h ⟨i,rfl⟩)

theorem coefficient_outside (n : ℤ) (hn : ∀ i, p i ≠ n) : coefficient V p n = 0 := by
  classical
  exact dite_eq_right (by simpa only [not_exists] using hn)

/-- Read the same family using another finite set of support degrees. -/
def reindex : (∀ i, V (p i)) →ₗ[R] (∀ j, V (q j)) :=
  LinearMap.pi (fun j => coefficient V p (q j))

@[simp] theorem reindex_apply (x : ∀ i, V (p i)) (j : Fin m) :
    reindex V p q x j = coefficient V p (q j) x := rfl

theorem coefficient_reindex (hq : Function.Injective q)
    (hV : ∀ n, (∀ j, q j ≠ n) → IsZero (V n))
    (n : ℤ) (x : ∀ i, V (p i)) :
    coefficient V q n (reindex V p q x) = coefficient V p n x := by
  classical
  by_cases h : ∃ j, q j=n
  · obtain ⟨j,rfl⟩ := h
    rw [coefficient_at V q hq,reindex_apply]
  · let := ModuleCat.subsingleton_of_isZero (hV n (by simpa only [not_exists] using h))
    exact Subsingleton.elim _ _

/-- Changing finite support indices adds or removes only zero terms. The maps
are the actual coordinate inclusions/projections, including all degree transports. -/
def equivalence (hp : Function.Injective p) (hq : Function.Injective q)
    (hVp : ∀ n, (∀ i, p i ≠ n) → IsZero (V n))
    (hVq : ∀ n, (∀ j, q j ≠ n) → IsZero (V n)) :
    (∀ i, V (p i)) ≃ₗ[R] (∀ j, V (q j)) where
  __ := reindex V p q
  invFun := reindex V q p
  left_inv x := by
    funext i
    change coefficient V q (p i) (reindex V p q x) = x i
    rw [coefficient_reindex V p q hq hVq,coefficient_at V p hp]
  right_inv x := by
    funext j
    change coefficient V p (q j) (reindex V q p x) = x j
    rw [coefficient_reindex V q p hp hVp,coefficient_at V q hq]
end LittleFinitistic.FiniteSupportReindex

end

end OAI
