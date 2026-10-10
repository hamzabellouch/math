import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Finset
open scoped RealInnerProductSpace
section FinitePatch
variable {X E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype A]

noncomputable def finitePatch (f : X → E) (g : A → X → E) (q : A → X → ℝ)
    (t : ℝ) (x : X) : E := f x + ∑ a, (t * q a x) • (g a x - f x)

lemma finitePatch_continuous [TopologicalSpace X] {f : X → E} {g : A → X → E} {q : A → X → ℝ}
    (hf : Continuous f) (hg : ∀ a, Continuous (g a)) (hq : ∀ a, Continuous (q a)) :
    Continuous (fun p : ℝ × X => finitePatch f g q p.1 p.2) := by
  apply (hf.comp continuous_snd).add
  apply continuous_finsetSum
  intro a _
  exact (continuous_fst.mul ((hq a).comp continuous_snd)).smul
    (((hg a).comp continuous_snd).sub (hf.comp continuous_snd))

lemma finitePatch_zero (f : X → E) (g : A → X → E) (q : A → X → ℝ) (x : X) :
    finitePatch f g q 0 x = f x := by simp [finitePatch]

lemma finitePatch_of_all_zero (f : X → E) (g : A → X → E) (q : A → X → ℝ)
    (t : ℝ) (x : X) (hq : ∀ a, q a x = 0) : finitePatch f g q t x = f x := by
  simp [finitePatch,hq]

lemma finitePatch_of_disjoint [DecidableEq A]
    (f : X → E) (g : A → X → E) (q : A → X → ℝ) (t : ℝ) (x : X) (a : A)
    (hq : ∀ a' ≠ a, q a' x = 0) :
    finitePatch f g q t x = (1-t*q a x) • f x + (t*q a x) • g a x := by
  unfold finitePatch
  rw [Finset.sum_eq_single a]
  · module
  · intro a' _ ha'
    simp [hq a' ha']
  · simp

lemma finitePatch_one_of_disjoint [DecidableEq A]
    (f : X → E) (g : A → X → E) (q : A → X → ℝ) (x : X) (a : A)
    (h1 : q a x = 1) (hq : ∀ a' ≠ a, q a' x = 0) :
    finitePatch f g q 1 x = g a x := by
  rw [finitePatch_of_disjoint f g q 1 x a hq,h1]
  simp

lemma finitePatch_cases [DecidableEq A] (f : X → E) (g : A → X → E)
    (q : A → X → ℝ) (t : ℝ) (x : X)
    (hq : Pairwise (fun a a' => Disjoint (Function.support (q a)) (Function.support (q a')))) :
    finitePatch f g q t x = f x ∨ ∃ a, q a x ≠ 0 ∧
      finitePatch f g q t x = (1-t*q a x) • f x + (t*q a x) • g a x := by
  by_cases hh : ∃ a, q a x ≠ 0
  · obtain ⟨a,ha⟩ := hh
    refine Or.inr ⟨a,ha,finitePatch_of_disjoint f g q t x a ?_⟩
    intro a' ha'
    by_contra hn
    exact Set.disjoint_left.mp (hq ha') hn ha
  · push Not at hh
    exact Or.inl (finitePatch_of_all_zero f g q t x hh)

lemma finitePatch_ne_zero [DecidableEq A] (f : X → E) (g : A → X → E)
    (q : A → X → ℝ) (t : ℝ) (x : X)
    (hq : Pairwise (fun a a' => Disjoint (Function.support (q a)) (Function.support (q a'))))
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hqb : ∀ a, q a x ∈ Set.Icc (0:ℝ) 1)
    (hf : f x ≠ 0)
    (hseg : ∀ a, q a x ≠ 0 → ∀ s ∈ Set.Icc (0:ℝ) 1,
      (1-s) • f x + s • g a x ≠ 0) : finitePatch f g q t x ≠ 0 := by
  rcases finitePatch_cases f g q t x hq with he | ⟨a,ha,he⟩
  · rwa [he]
  · rw [he]
    exact hseg a ha (t*q a x) ⟨mul_nonneg ht.1 (hqb a).1,
      (mul_le_mul_of_nonneg_left (hqb a).2 ht.1).trans (by simpa using ht.2)⟩

end FinitePatch

end BorsukNine

end OAI
