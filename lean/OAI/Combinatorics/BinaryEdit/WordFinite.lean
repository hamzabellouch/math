import OAI.Combinatorics.BinaryEdit.Model
import Mathlib.Data.Fintype.Vector
import Mathlib.Basic.Finite.Sigma
import Mathlib.Tactic

namespace OAI

namespace TreeEdit.BinaryLower

universe u
variable {α : Type u}

/-- Exact-length words form a finite type over every finite alphabet. -/
instance wordFinite [Finite α] (n : ℕ) : Finite (Word α n) :=
  inferInstanceAs (Finite (List.Vector α n))

/-- At-most-length words form a finite type; the length is retained as a
finite sigma index, so repetitions and the empty word are included. -/
instance wordsLEFinite [Finite α] (d : ℕ) : Finite (WordsLE α d) := by
  let f : WordsLE α d → Σ n : Fin (d + 1), Word α n.val :=
    fun x => ⟨⟨x.val.length, Nat.lt_succ_of_le x.property⟩, ⟨x.val, rfl⟩⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Σ n : Fin (d + 1), Word α n.val => z.2.val) h

/-- The empty word is included even at cap zero. -/
instance wordsLEInhabited (d : ℕ) : Inhabited (WordsLE α d) :=
  ⟨⟨[], by simp⟩⟩

/-- A positive cap and a nonempty alphabet already give two distinct words. -/
theorem wordsLE_nontrivial [Nonempty α] {d : ℕ} (hd : 1 ≤ d) :
    Nontrivial (WordsLE α d) := by
  classical
  let a : α := Classical.choice inferInstance
  refine ⟨⟨⟨[], by simp⟩, ⟨[a], by simpa using hd⟩, ?_⟩⟩
  intro h
  have := congrArg (fun x : WordsLE α d => x.val.length) h
  simp at this

end TreeEdit.BinaryLower

end OAI
