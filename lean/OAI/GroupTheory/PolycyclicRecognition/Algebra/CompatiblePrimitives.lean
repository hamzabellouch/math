import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic

namespace OAI

/-! # Compatible primitives along a countable tower

A primitive at the next stage can be corrected by a coboundary to agree
with the previous one. This is the algebraic step in the dimension bound
for a countable increasing union of subgroups.
-/

noncomputable section
namespace PolycyclicRecognition

theorem exists_compatible_primitives
    {X Y Z : ℕ → Type*}
    [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)] [∀ n, AddCommGroup (Z n)]
    (d : ∀ n, X n →+ Y n) (e : ∀ n, Y n →+ Z n)
    (rX : ∀ n, X (n + 1) →+ X n) (rY : ∀ n, Y (n + 1) →+ Y n)
    (rZ : ∀ n, Z (n + 1) →+ Z n)
    (hd : ∀ n x, rY n (d (n + 1) x) = d n (rX n x))
    (he : ∀ n y, rZ n (e (n + 1) y) = e n (rY n y))
    (hzero : ∀ n x, e n (d n x) = 0)
    (hexact : ∀ n y, e n y = 0 → ∃ x, d n x = y)
    (hsurj : ∀ n, Function.Surjective (rX n))
    (z : ∀ n, Z n) (hz : ∀ n, rZ n (z (n + 1)) = z n)
    (hprim : ∀ n, ∃ y, e n y = z n) :
    ∃ y : ∀ n, Y n, (∀ n, e n (y n) = z n) ∧
      ∀ n, rY n (y (n + 1)) = y n := by
  have step (n : ℕ) (y : Y n) (hy : e n y = z n) :
      ∃ y' : Y (n + 1), e (n + 1) y' = z (n + 1) ∧ rY n y' = y := by
    obtain ⟨v, hv⟩ := hprim (n + 1)
    have hvy : e n (rY n v - y) = 0 := by
      rw [map_sub, ← he, hv, hz, hy, sub_self]
    obtain ⟨w, hw⟩ := hexact n _ hvy
    obtain ⟨w', hw'⟩ := hsurj n w
    refine ⟨v - d (n + 1) w', ?_, ?_⟩
    · rw [map_sub, hzero, sub_zero, hv]
    · rw [map_sub, hd, hw', hw, sub_sub_cancel]
  let start : {y : Y 0 // e 0 y = z 0} :=
    ⟨(hprim 0).choose, (hprim 0).choose_spec⟩
  let next (n : ℕ) (y : {y : Y n // e n y = z n}) :
      {y : Y (n + 1) // e (n + 1) y = z (n + 1)} :=
    ⟨(step n y y.property).choose, (step n y y.property).choose_spec.1⟩
  let ys : ∀ n, {y : Y n // e n y = z n} := Nat.rec start next
  refine ⟨fun n => (ys n).val, fun n => (ys n).property, ?_⟩
  intro n
  exact (step n (ys n).val (ys n).property).choose_spec.2

end PolycyclicRecognition

end

end OAI
