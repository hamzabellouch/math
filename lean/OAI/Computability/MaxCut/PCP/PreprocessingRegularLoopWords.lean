import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-!
# Prefix and suffix invariants for regular-table row loops

These finite block identities apply to original-vertex blocks, to dummy blocks
within an owner, and to whole owner blocks. They expose exactly the next emitted
block while preserving the codec's established order.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularLoopWords

/-- Bits emitted by the first `k` blocks. -/
def blocksPrefix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).take k).flatten

/-- Bits remaining after the first `k` blocks. -/
def blocksSuffix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).drop k).flatten

@[simp] theorem blocksPrefix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f 0 = [] := by
  simp only [blocksPrefix, List.take_zero, List.flatten_nil]

@[simp] theorem blocksPrefix_all {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f n = (List.ofFn f).flatten := by
  have h : (List.ofFn f).take n = List.ofFn f := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksPrefix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksPrefix f (k + 1) = blocksPrefix f k ++ f ⟨k, h⟩ := by
  unfold blocksPrefix
  rw [List.take_succ_eq_append_getElem
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.getElem_ofFn]

@[simp] theorem blocksSuffix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f 0 = (List.ofFn f).flatten := by
  simp only [blocksSuffix, List.drop_zero]

@[simp] theorem blocksSuffix_all {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f n = [] := by
  have h : (List.ofFn f).drop n = [] := by
    simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksSuffix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksSuffix f k = f ⟨k, h⟩ ++ blocksSuffix f (k + 1) := by
  unfold blocksSuffix
  rw [List.drop_eq_getElem_cons
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_cons, List.getElem_ofFn]

/-- The completed and remaining portions partition the original bitstream. -/
theorem blocksPrefix_append_suffix {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    blocksPrefix f k ++ blocksSuffix f k = (List.ofFn f).flatten := by
  unfold blocksPrefix blocksSuffix
  rw [← List.flatten_append, List.take_append_drop]

end MaxCutGames.Foundations.PCP.PreprocessingRegularLoopWords

end OAI
