import OAI.Combinatorics.DiscreteConvexity.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-!
# Grouping and repeating union tuples

Grouping `a * b` entries into `a` rows of length `b` preserves exactly the
possible unions. Repetition is allowed throughout, as in the definition of
the exceptional family. No positivity assumption is needed for grouping.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Flatten a rectangular array using the standard finite product equivalence. -/
def flattenTuple {a b : ℕ} (f : Fin a → Fin b → Finset α) :
    Fin (a * b) → Finset α :=
  fun t => f (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2

omit [Fintype α] in
theorem unionTuple_flatten {a b : ℕ} (f : Fin a → Fin b → Finset α) :
    unionTuple (flattenTuple f) = unionTuple (fun i => unionTuple (f i)) := by
  ext x
  simp only [mem_unionTuple]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2, ht⟩
  · rintro ⟨i, j, hij⟩
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simpa only [flattenTuple, Equiv.symm_apply_apply] using hij

omit [Fintype α] in
theorem unionTuple_rows {a b : ℕ} (f : Fin (a * b) → Finset α) :
    unionTuple (fun i : Fin a => unionTuple (fun j : Fin b => f (finProdFinEquiv (i, j)))) =
      unionTuple f := by
  rw [← unionTuple_flatten]
  apply congrArg (fun g : Fin (a * b) → Finset α => unionTuple g)
  funext t
  exact congrArg f (finProdFinEquiv.apply_symm_apply t)

/-- Iterated unions are exactly unions of the product number of entries. -/
theorem unionFamily_mul (a b : ℕ) (D : Family α) :
    unionFamily a (unionFamily b D) = unionFamily (a * b) D := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨f, hf, hfS⟩ := mem_unionFamily.mp hS
    have hrows : ∀ i : Fin a, ∃ g : Fin b → Finset α,
        (∀ j, g j ∈ D) ∧ unionTuple g = f i :=
      fun i => mem_unionFamily.mp (hf i)
    choose g hg hgUnion using hrows
    apply mem_unionFamily.mpr
    refine ⟨flattenTuple g, ?_, ?_⟩
    · intro t
      exact hg (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
    · rw [unionTuple_flatten]
      have hfun : (fun i => unionTuple (g i)) = f := funext hgUnion
      rw [hfun]
      exact hfS
  · intro hS
    obtain ⟨f, hf, hfS⟩ := mem_unionFamily.mp hS
    apply mem_unionFamily.mpr
    refine ⟨fun i : Fin a => unionTuple (fun j : Fin b => f (finProdFinEquiv (i, j))),
      ?_, ?_⟩
    · intro i
      exact mem_unionFamily.mpr
        ⟨fun j => f (finProdFinEquiv (i, j)), fun j => hf _, rfl⟩
    · rw [unionTuple_rows]
      exact hfS

/-- Grouping tuples preserves failure of containment in every possible union. -/
theorem exceptional_unionFamily (a b : ℕ) (D : Family α) :
    exceptional a (unionFamily b D) = exceptional (a * b) D := by
  ext S
  simp only [mem_exceptional_iff_unionFamily, unionFamily_mul]

/-- Repeat the same row tuple `a` times. -/
def repeatTuple (a : ℕ) {b : ℕ} (f : Fin b → Finset α) :
    Fin (a * b) → Finset α :=
  flattenTuple (fun _ : Fin a => f)

omit [Fintype α] [DecidableEq α] in
theorem repeatTuple_mem {a b : ℕ} {D : Family α} (f : Fin b → Finset α)
    (hf : ∀ j, f j ∈ D) (t : Fin (a * b)) : repeatTuple a f t ∈ D :=
  hf (finProdFinEquiv.symm t).2

omit [Fintype α] in
theorem unionTuple_repeat {a b : ℕ} (ha : 0 < a) (f : Fin b → Finset α) :
    unionTuple (repeatTuple a f) = unionTuple f := by
  rw [repeatTuple, unionTuple_flatten]
  ext x
  simp only [mem_unionTuple]
  constructor
  · rintro ⟨_, j, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨⟨0, ha⟩, j, hj⟩

theorem exists_unionTuple_mul_eq_univ {a b : ℕ} (ha : 0 < a) {D : Family α}
    (f : Fin b → Finset α) (hf : ∀ j, f j ∈ D)
    (hfull : unionTuple f = Finset.univ) :
    ∃ g : Fin (a * b) → Finset α, (∀ j, g j ∈ D) ∧ unionTuple g = Finset.univ := by
  refine ⟨repeatTuple a f, repeatTuple_mem f hf, ?_⟩
  rw [unionTuple_repeat ha, hfull]

theorem exceptional_mul_eq_empty_of_full_union {a b : ℕ} (ha : 0 < a) {D : Family α}
    (f : Fin b → Finset α) (hf : ∀ j, f j ∈ D)
    (hfull : unionTuple f = Finset.univ) : exceptional (a * b) D = ∅ := by
  obtain ⟨g, hg, hgfull⟩ := exists_unionTuple_mul_eq_univ ha f hf hfull
  exact exceptional_eq_empty_of_full_union g hg hgfull

/-- The repetition used in the full-union branch of the density argument. -/
theorem exists_unionTuple_thirtytwo_mul_eq_univ {L : ℕ} {D : Family α}
    (f : Fin L → Finset α) (hf : ∀ j, f j ∈ D)
    (hfull : unionTuple f = Finset.univ) :
    ∃ g : Fin (32 * L) → Finset α, (∀ j, g j ∈ D) ∧ unionTuple g = Finset.univ :=
  exists_unionTuple_mul_eq_univ (by decide : 0 < 32) f hf hfull

end TalagrandDiscreteConvexity

end OAI
