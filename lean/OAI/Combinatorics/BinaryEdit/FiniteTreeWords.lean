import OAI.Combinatorics.BinaryEdit.Model
import Mathlib

namespace OAI

/-!
# Recursive row words for the finite tree

The recursion in equation (finite-word) uses an additive state group,
node shifts and leaf symbols. It is instantiated with the product of
cyclic groups in the manuscript.
-/

namespace TreeEdit.BinaryLower.FiniteTree

variable {A Γ : Type*} [AddCommMonoid A]

/-- A row is the ordered concatenation of the `m` child words.  At a leaf the
word consists of its single tagged state symbol. -/
def nodeWord {m : ℕ} (T : ℕ) (leaf : List (Fin m) → A → Γ)
    (u : List (Fin m) → A) : ℕ → List (Fin m) → A → List Γ
  | 0, p, x => [leaf p x]
  | h + 1, p, x => (List.range T).flatMap fun a =>
      (List.finRange m).flatMap fun i => nodeWord T leaf u h (p ++ [i]) (x + a • u p)

/-- All node words at a given height have exactly the manuscript's length. -/
@[simp] theorem nodeWord_length {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) :
    (nodeWord T leaf u h p x).length = (m * T) ^ h := by
  induction h generalizing p x with
  | zero => simp [nodeWord]
  | succ h ih =>
      simp only [nodeWord, List.length_flatMap, ih]
      simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- One row at a node of height `h+1`. -/
def nodeRow {m : ℕ} (T : ℕ) (leaf : List (Fin m) → A → Γ)
    (u : List (Fin m) → A) (h : ℕ) (p : List (Fin m)) (x : A) : List Γ :=
  (List.finRange m).flatMap fun i => nodeWord T leaf u h (p ++ [i]) x

@[simp] theorem nodeRow_length {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) :
    (nodeRow T leaf u h p x).length = m * (m * T) ^ h := by
  simp [nodeRow, List.length_flatMap]

/-- Translating by the cheap vector advances the row parameter. -/
theorem nodeWord_translate {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) (s : ℕ) :
    nodeWord T leaf u (h + 1) p (x + s • u p) =
      (List.range T).flatMap fun a => nodeRow T leaf u h p (x + (s + a) • u p) := by
  simp only [nodeWord, nodeRow, add_nsmul, add_assoc]

/-- A translation invisible at every descendant leaf is invisible in the
complete recursive word. The hypothesis is required for all states, permitting
all ancestor offsets without adding any invariance assumption on the shifts. -/
theorem nodeWord_invariant {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (z : A)
    (hinv : ∀ q : List (Fin m), q.length = h → ∀ x : A,
      leaf (p ++ q) (x + z) = leaf (p ++ q) x) (x : A) :
    nodeWord T leaf u h p (x + z) = nodeWord T leaf u h p x := by
  induction h generalizing p x with
  | zero =>
      have hi := hinv [] rfl x
      simpa [nodeWord] using congrArg (fun a => [a]) hi
  | succ h ih =>
      simp only [nodeWord]
      apply List.flatMap_congr
      intro a ha
      apply List.flatMap_congr
      intro i hi
      rw [add_right_comm x z]
      apply ih
      intro q hq y
      have he : ([i] ++ q).length = h + 1 := by simp [hq]
      simpa [List.append_assoc] using hinv ([i] ++ q) he y

end TreeEdit.BinaryLower.FiniteTree

end OAI
