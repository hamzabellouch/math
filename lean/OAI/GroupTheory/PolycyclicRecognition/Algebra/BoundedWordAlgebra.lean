import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.List.OfFn

namespace OAI

/-! # Finite algebras from a bound on generator products

This is the finite-dimensionality step for the truncated enveloping algebra
used to extend a nilpotent representation by derivations.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]
  {ι : Type*} [Fintype ι] (j : ι → A) (c : ℕ)

/-- Products with at most the specified number of letters. -/
def boundedWordProducts : Set A :=
  Set.range (fun w : Σ k : Fin (c + 1), Fin k → ι => (List.ofFn (fun i => j (w.2 i))).prod)

theorem boundedWordProducts_finite : (boundedWordProducts j c).Finite :=
  Set.finite_range _

omit [Fintype ι] in
theorem list_prod_mem_boundedWordSpan
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) (l : List ι) :
    (l.map j).prod ∈ Submodule.span R (boundedWordProducts j c) := by
  by_cases hl : l.length ≤ c
  · apply Submodule.subset_span
    refine ⟨⟨⟨l.length, Nat.lt_succ_of_le hl⟩, l.get⟩, ?_⟩
    change (List.ofFn (j ∘ l.get)).prod = _
    rw [← List.map_ofFn, List.ofFn_get]
  · rw [hnil l (Nat.lt_of_not_ge hl)]
    exact Submodule.zero_mem _

omit [Fintype ι] in
theorem adjoin_le_boundedWordSpan
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) :
    (Algebra.adjoin R (Set.range j)).toSubmodule ≤
      Submodule.span R (boundedWordProducts j c) := by
  rw [Algebra.adjoin_eq_span]
  apply Submodule.span_le.mpr
  intro x hx
  have hword : ∃ l : List ι, (l.map j).prod = x := by
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨[i], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := hy
      exact ⟨l ++ k, by simp⟩
  obtain ⟨l, rfl⟩ := hword
  exact list_prod_mem_boundedWordSpan j c hnil l

theorem finiteDimensional_of_bounded_generator_products
    (hgen : Algebra.adjoin R (Set.range j) = ⊤)
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) :
    FiniteDimensional R A := by
  have hspan : Submodule.span R (boundedWordProducts j c) = ⊤ := by
    apply top_unique
    have h := adjoin_le_boundedWordSpan (R := R) j c hnil
    rw [hgen] at h
    exact h
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span (boundedWordProducts_finite j c)

end PolycyclicRecognition

end

end OAI
