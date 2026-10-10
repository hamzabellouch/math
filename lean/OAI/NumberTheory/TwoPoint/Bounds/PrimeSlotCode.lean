import OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords

namespace OAI

/-! A complete equality-pattern code for tuple and padding prime occurrences. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- Each occurrence records its step, whether it belongs to the padding,
and its numerical prime. Unused slots are avoided by taking the actual total length. -/
structure PrimeSlotData (R N : ℕ) where
  forward : Fin R → Bool
  row : Fin N → Fin R
  isPadding : Fin N → Bool
  prime : Fin N → ℕ

namespace PrimeSlotData

variable {R N : ℕ}

def slots (a : PrimeSlotData R N) (i : Fin R) (b : Bool) : Finset (Fin N) :=
  univ.filter (fun j => a.row j = i ∧ a.isPadding j = b)

def factor (a : PrimeSlotData R N) (i : Fin R) (b : Bool) : ℕ :=
  ∏ j ∈ a.slots i b, a.prime j

def word (a : PrimeSlotData R N) : List SignedStep :=
  List.ofFn (fun i => ⟨a.forward i, a.factor i false, a.factor i true⟩)

noncomputable def code (a : PrimeSlotData R N) : CrudeWordCode R N R :=
  (a.forward, columnRepresentative a.prime ∅, a.row, a.isPadding)

lemma code_class_eq_iff (a : PrimeSlotData R N) (i j : Fin N) :
    a.code.2.1 i = a.code.2.1 j ↔ a.prime i = a.prime j :=
  columnRepresentative_eq_iff a.prime ∅ i j

lemma code_class_prime (a : PrimeSlotData R N) (i : Fin N) :
    a.prime (a.code.2.1 i) = a.prime i :=
  columnRepresentative_label a.prime ∅ i

end PrimeSlotData

namespace CrudeWordCode

variable {R N : ℕ}

def usedClasses (c : CrudeWordCode R N R) : Finset (Fin N) := univ.image c.2.1

def classAt (c : CrudeWordCode R N R) (i : Fin N) : c.usedClasses :=
  ⟨c.2.1 i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩

def primeData (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) : PrimeSlotData R N where
  forward := c.1
  row := c.2.2.1
  isPadding := c.2.2.2
  prime i := value (c.classAt i)

def numericalWord (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) : List SignedStep :=
  (c.primeData value).word

lemma primeData_encode (a : PrimeSlotData R N) :
    a.code.primeData (fun c => a.prime c.val) = a := by
  cases a with
  | mk forward row isPadding prime =>
      unfold primeData PrimeSlotData.code
      congr 1
      funext i
      exact columnRepresentative_label prime ∅ i

lemma numericalWord_encode (a : PrimeSlotData R N) :
    a.code.numericalWord (fun c => a.prime c.val) = a.word := by
  exact congrArg PrimeSlotData.word (primeData_encode a)

lemma numericalWord_length (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) :
    (c.numericalWord value).length = R := by
  simp [numericalWord, PrimeSlotData.word]

/-- Padding is reconstructed from the same prime classes as tuple factors,
so repetitions across steps never introduce new independent numerical choices. -/
lemma numericalWord_get (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) (i : Fin R) :
    (c.numericalWord value)[i.val]'(by rw [numericalWord_length]; exact i.isLt) =
      ⟨c.1 i,
        ∏ j ∈ univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = false), value (c.classAt j),
        ∏ j ∈ univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = true), value (c.classAt j)⟩ := by
  simp [numericalWord, PrimeSlotData.word, PrimeSlotData.factor, PrimeSlotData.slots, primeData]
  constructor <;> congr 1

end CrudeWordCode

end TwoPointCorrelations

end OAI
