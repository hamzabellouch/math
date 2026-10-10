import OAI.Computability.PerfectCompleteness.Construction.FactoredFunctionsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.UniformChildSum

namespace OAI


namespace PerfectCompleteness.LocalReconstruction

open scoped BigOperators
open PointwiseSpaces RecursiveSpaces FactoredFunctions

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] {branch : Nat → Nat} {n : Nat}

abbrev Retained (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) :=
  (j : {j : Fin (branch n) // ¬ clean j}) → Assignment (childFamily A j.1)

def retain (A : Slots branch (n + 1) → Type*) (clean : Fin (branch n) → Prop) :
    Assignment A → Retained A clean :=
  fun x j => childRestriction A j.1 x

abbrev Summands (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) :=
  (j : {j : Fin (branch n) // ¬ clean j}) →
    squareSpace (space 𝕜 branch n (childFamily A j.1))

def retainedCut (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) [DecidablePred clean]
    (u : Summands (𝕜 := 𝕜) A clean) : Retained A clean → 𝕜 :=
  fun x => ∑ j, (u j).val (x j)

def cutCall (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) [DecidablePred clean]
    (u : Summands (𝕜 := 𝕜) A clean) : space 𝕜 branch (n + 1) A :=
  ⟨∑ j, pullback 𝕜 (childRestriction A j.1) (u j).val, by
    apply (space 𝕜 branch (n + 1) A).sum_mem
    intro j _
    exact child_square_le_space A j.1 (Submodule.mem_map_of_mem (u j).property)⟩

theorem cutCall_factors (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) [DecidablePred clean]
    (u : Summands (𝕜 := 𝕜) A clean) :
    (cutCall A clean u).val = retainedCut A clean u ∘ retain A clean := by
  funext x
  simp only [cutCall, retainedCut, retain, Function.comp_apply,
    Finset.sum_apply, PointwiseSpaces.pullback_apply]

theorem cutCall_ignores_clean (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) [DecidablePred clean]
    (u : Summands (𝕜 := 𝕜) A clean) :
    (cutCall A clean u).val ∈ factoringSpace (retain A clean) := by
  rw [mem_factoringSpace_iff_exists_factor]
  exact ⟨retainedCut A clean u, fun x => congrFun (cutCall_factors A clean u) x⟩

theorem actual_sum_eq_cutCall (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) [DecidablePred clean]
    (u : (j : Fin (branch n)) → squareSpace (space 𝕜 branch n (childFamily A j)))
    (zero : ∀ j, clean j → u j = 0) :
    UniformChildSum.recursiveSum A u = cutCall A clean (fun j => u j.1) := by
  apply Subtype.ext
  change (∑ j : Fin (branch n), pullback 𝕜 (childRestriction A j) (u j).val) = _
  rw [← Fintype.sum_subtype_add_sum_subtype clean
    (fun j => pullback 𝕜 (childRestriction A j) (u j).val)]
  have hz : (∑ j : {j : Fin (branch n) // clean j},
      pullback 𝕜 (childRestriction A j.1) (u j.1).val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [zero j.1 j.2]
    exact map_zero _
  rw [hz, zero_add]
  rfl

theorem actual_sum_ignores_clean (A : Slots branch (n + 1) → Type*)
    (clean : Fin (branch n) → Prop) [DecidablePred clean]
    (u : (j : Fin (branch n)) → squareSpace (space 𝕜 branch n (childFamily A j)))
    (zero : ∀ j, clean j → u j = 0) :
    (UniformChildSum.recursiveSum A u).val ∈ factoringSpace (retain A clean) := by
  rw [actual_sum_eq_cutCall A clean u zero]
  exact cutCall_ignores_clean A clean _

inductive Recipe (𝕜 Atom : Type*) where
  | constant : 𝕜 → Recipe 𝕜 Atom
  | atom : Atom → Recipe 𝕜 Atom
  | add : Recipe 𝕜 Atom → Recipe 𝕜 Atom → Recipe 𝕜 Atom
  | mul : Recipe 𝕜 Atom → Recipe 𝕜 Atom → Recipe 𝕜 Atom

namespace Recipe

variable {Atom X Z : Type*}

def evaluate (atoms : Atom → X → 𝕜) : Recipe 𝕜 Atom → X → 𝕜
  | .constant c => fun _ => c
  | .atom a => atoms a
  | .add f g => evaluate atoms f + evaluate atoms g
  | .mul f g => evaluate atoms f * evaluate atoms g

theorem evaluate_factors (other : X → Z) (atoms : Atom → X → 𝕜)
    (known : ∀ a, atoms a ∈ factoringSpace other) (r : Recipe 𝕜 Atom) :
    r.evaluate atoms ∈ factoringSpace other := by
  induction r with
  | constant c => exact const_mem_factoringSpace other c
  | atom a => exact known a
  | add f g hf hg => exact (factoringSpace other).add_mem hf hg
  | mul f g hf hg => exact mul_mem_factoringSpace other hf hg

theorem evaluate_pullback (other : X → Z) (atoms : Atom → Z → 𝕜)
    (r : Recipe 𝕜 Atom) :
    r.evaluate (fun a => atoms a ∘ other) = r.evaluate atoms ∘ other := by
  induction r with
  | constant c => rfl
  | atom a => rfl
  | add f g hf hg =>
      simp only [evaluate, hf, hg]
      rfl
  | mul f g hf hg =>
      simp only [evaluate, hf, hg]
      rfl

end Recipe

end
end PerfectCompleteness.LocalReconstruction

end OAI
