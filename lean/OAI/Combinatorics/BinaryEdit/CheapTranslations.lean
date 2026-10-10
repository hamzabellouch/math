import OAI.Combinatorics.BinaryEdit.Model
import Mathlib.Data.List.Range
import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Inexpensive translations

Elementary unrestricted edit scripts give the translation estimates in
`lem:finite-cost`.
-/

namespace TreeEdit.BinaryLower.CheapTranslations

universe u v

variable {α : Type u}

theorem unitEdit_prefix {x y : List α} (p : List α)
    (h : EditStep x y) : EditStep (p ++ x) (p ++ y) := by
  cases h with
  | insert q s a =>
      simpa only [List.append_assoc] using EditStep.insert (p ++ q) s a
  | delete q s a =>
      simpa only [List.append_assoc] using EditStep.delete (p ++ q) s a
  | substitute q s a b =>
      simpa only [List.append_assoc] using EditStep.substitute (p ++ q) s a b

theorem script_prefix {x y : List α} {n : ℕ} (p : List α)
    (h : EditScript x y n) : EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil x => exact EditScript.nil _
  | cons step tail ih => exact EditScript.cons (unitEdit_prefix p step) ih

theorem unitEdit_suffix {x y : List α} (q : List α)
    (h : EditStep x y) : EditStep (x ++ q) (y ++ q) := by
  cases h with
  | insert p s a =>
      simpa only [List.append_assoc, List.cons_append] using
        EditStep.insert p (s ++ q) a
  | delete p s a =>
      simpa only [List.append_assoc, List.cons_append] using
        EditStep.delete p (s ++ q) a
  | substitute p s a b =>
      simpa only [List.append_assoc, List.cons_append] using
        EditStep.substitute p (s ++ q) a b

theorem script_suffix {x y : List α} {n : ℕ} (q : List α)
    (h : EditScript x y n) : EditScript (x ++ q) (y ++ q) n := by
  induction h with
  | nil x => exact EditScript.nil _
  | cons step tail ih => exact EditScript.cons (unitEdit_suffix q step) ih

theorem script_trans {x y z : List α} {m n : ℕ}
    (hxy : EditScript x y m) (hyz : EditScript y z n) :
    EditScript x z (m + n) := by
  induction hxy with
  | nil x => simpa using hyz
  | cons step tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EditScript.cons step (ih hyz)

theorem script_delete_prefix (p x : List α) :
    EditScript (p ++ x) x p.length := by
  induction p with
  | nil => exact EditScript.nil x
  | cons a p ih =>
      exact EditScript.cons (EditStep.delete [] (p ++ x) a) ih

theorem script_insert_prefix (p x : List α) :
    EditScript x (p ++ x) p.length := by
  induction p with
  | nil => exact EditScript.nil x
  | cons a p ih =>
      exact EditScript.cons (EditStep.insert [] x a) (script_prefix [a] ih)

theorem script_insert_suffix (x s : List α) :
    EditScript x (x ++ s) s.length := by
  simpa using script_prefix x (script_insert_prefix s [])

theorem editDistance_le_script {x y : List α} {n : ℕ}
    (h : EditScript x y n) : ed x y ≤ n := by
  exact csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ h

/-- Retain a common middle word, delete the initial segment and insert the
terminal segment. Intermediate words are not subject to any length cap. -/
theorem editDistance_prefix_suffix (p x s : List α) :
    ed (p ++ x) (x ++ s) ≤ p.length + s.length := by
  exact editDistance_le_script
    (script_trans (script_delete_prefix p x) (script_insert_suffix x s))

/-- A consecutive finite window of rows, concatenated in increasing order. -/
def rowWindow (rows : ℕ → List α) (start count : ℕ) : List α :=
  (List.range' start count).flatMap rows

theorem rowWindow_add (rows : ℕ → List α) (a m n : ℕ) :
    rowWindow rows a (m + n) =
      rowWindow rows a m ++ rowWindow rows (a + m) n := by
  unfold rowWindow
  rw [← List.range'_append_1, List.flatMap_append]

theorem rowWindow_shift_index (rows : ℕ → List α) (a s n : ℕ) :
    rowWindow (fun j => rows (s + j)) a n = rowWindow rows (s + a) n := by
  induction n generalizing a with
  | zero => simp [rowWindow]
  | succ n ih =>
      simp only [rowWindow, List.range'_succ, List.flatMap_cons]
      change rows (s + a) ++ rowWindow (fun j => rows (s + j)) (a + 1) n =
        rows (s + a) ++ rowWindow rows (s + a + 1) n
      rw [ih, Nat.add_assoc]

theorem rowWindow_length (rows : ℕ → List α) (a n B : ℕ)
    (hlen : ∀ j, (rows j).length = B) :
    (rowWindow rows a n).length = n * B := by
  induction n generalizing a with
  | zero => simp [rowWindow]
  | succ n ih =>
      simp only [rowWindow, List.range'_succ, List.flatMap_cons,
        List.length_append, hlen]
      change B + (rowWindow rows (a + 1) n).length = (n + 1) * B
      rw [ih]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- An explicit script for sliding a fixed number of rows. Its exact cost is
useful when the same local operation is repeated in a larger concatenation. -/
theorem script_rowWindow_shift (rows : ℕ → List α)
    (a T s B : ℕ) (hs : s ≤ T)
    (hlen : ∀ j, (rows j).length = B) :
    EditScript (rowWindow rows a T) (rowWindow rows (a + s) T)
      (2 * s * B) := by
  have hleft := rowWindow_add rows a s (T - s)
  have hright := rowWindow_add rows (a + s) (T - s) s
  rw [Nat.add_sub_of_le hs] at hleft
  rw [Nat.sub_add_cancel hs] at hright
  rw [hleft, hright]
  have h := script_trans
    (script_delete_prefix (rowWindow rows a s)
      (rowWindow rows (a + s) (T - s)))
    (script_insert_suffix (rowWindow rows (a + s) (T - s))
      (rowWindow rows (a + s + (T - s)) s))
  have hcost : (rowWindow rows a s).length +
      (rowWindow rows (a + s + (T - s)) s).length = 2 * s * B := by
    rw [rowWindow_length rows a s B hlen,
      rowWindow_length rows (a + s + (T - s)) s B hlen]
    simp only [two_mul, Nat.add_mul]
  rw [hcost] at h
  exact h

/-- Sliding `T` equally long rows by `s ≤ T` retains the middle `T-s`
rows and costs at most `2*s*B` edits. -/
theorem editDistance_rowWindow_shift (rows : ℕ → List α)
    (a T s B : ℕ) (hs : s ≤ T)
    (hlen : ∀ j, (rows j).length = B) :
    ed (rowWindow rows a T) (rowWindow rows (a + s) T) ≤
      2 * s * B :=
  editDistance_le_script (script_rowWindow_shift rows a T s B hs hlen)

/-- The row word arising from repeated translation in an additive parameter
space. This is the row operation in both tree constructions. -/
def orbitRows {A : Type v} [AddMonoid A] (row : A → List α)
    (x u : A) (T : ℕ) : List α :=
  rowWindow (fun j => row (x + j • u)) 0 T

theorem orbitRows_shift {A : Type v} [AddMonoid A] (row : A → List α)
    (x u : A) (T s : ℕ) :
    orbitRows row (x + s • u) u T =
      rowWindow (fun j => row (x + j • u)) s T := by
  unfold orbitRows
  have hfun : (fun j : ℕ => row (x + s • u + j • u)) =
      (fun j : ℕ => row (x + (s + j) • u)) := by
    funext j
    rw [add_nsmul, add_assoc]
  rw [hfun]
  simpa only [Nat.add_zero] using
    rowWindow_shift_index (fun j => row (x + j • u)) 0 s T

/-- An additive state translation by `s*u` is the exact row-window script,
also when `x` already includes offsets contributed by ancestor nodes. -/
theorem script_orbitRows_shift {A : Type v} [AddMonoid A]
    (row : A → List α) (x u : A) (T s B : ℕ) (hs : s ≤ T)
    (hlen : ∀ y, (row y).length = B) :
    EditScript (orbitRows row x u T) (orbitRows row (x + s • u) u T)
      (2 * s * B) := by
  rw [orbitRows_shift]
  simpa only [orbitRows, Nat.zero_add] using
    script_rowWindow_shift (fun j => row (x + j • u)) 0 T s B hs
      (fun j => hlen _)

theorem editDistance_orbitRows_shift {A : Type v} [AddMonoid A]
    (row : A → List α) (x u : A) (T s B : ℕ) (hs : s ≤ T)
    (hlen : ∀ y, (row y).length = B) :
    ed (orbitRows row x u T) (orbitRows row (x + s • u) u T) ≤
      2 * s * B :=
  editDistance_le_script (script_orbitRows_shift row x u T s B hs hlen)

/-- Substituting exactly the differing positions gives a script whose cost
is the Hamming mismatch count; repeated positions in `xs` are counted with
their multiplicity, as required for leaf occurrences in the tree words. -/
theorem script_map_mismatches {β : Type v} [DecidableEq β]
    (xs : List α) (f g : α → β) :
    EditScript (xs.map f) (xs.map g)
      (xs.countP fun a => decide (f a ≠ g a)) := by
  induction xs with
  | nil => exact EditScript.nil []
  | cons a xs ih =>
      by_cases h : f a = g a
      · simpa [List.countP_cons, h] using script_prefix [f a] ih
      · simpa [List.countP_cons, h] using
          EditScript.cons (EditStep.substitute [] (xs.map f) (f a) (g a))
            (script_prefix [g a] ih)

theorem editDistance_map_le_mismatches {β : Type v} [DecidableEq β]
    (xs : List α) (f g : α → β) :
    ed (xs.map f) (xs.map g) ≤
      xs.countP (fun a => decide (f a ≠ g a)) :=
  editDistance_le_script (script_map_mismatches xs f g)

/-- If a change is supported on a Boolean predicate, one substitution at each
supported occurrence suffices. No decidable equality on the output alphabet
is needed, and harmless substitutions at unchanged supported occurrences are
allowed by the ordinary-script definition. -/
theorem script_map_supported {β : Type v} (xs : List α)
    (f g : α → β) (p : α → Bool)
    (hfg : ∀ a ∈ xs, p a = false → f a = g a) :
    EditScript (xs.map f) (xs.map g) (xs.countP p) := by
  induction xs with
  | nil => exact EditScript.nil []
  | cons a xs ih =>
      have ht : ∀ b ∈ xs, p b = false → f b = g b := by
        intro b hb
        exact hfg b (List.mem_cons_of_mem a hb)
      cases hp : p a with
      | false =>
          have ha := hfg a (List.mem_cons_self) hp
          simpa [List.countP_cons, hp, ha] using script_prefix [f a] (ih ht)
      | true =>
          simpa [List.countP_cons, hp] using
            EditScript.cons (EditStep.substitute [] (xs.map f) (f a) (g a))
              (script_prefix [g a] (ih ht))

theorem editDistance_map_le_support {β : Type v} (xs : List α)
    (f g : α → β) (p : α → Bool)
    (hfg : ∀ a ∈ xs, p a = false → f a = g a) :
    ed (xs.map f) (xs.map g) ≤ xs.countP p :=
  editDistance_le_script (script_map_supported xs f g p hfg)

/-- Scripts in corresponding concatenated blocks add their costs. This
allows a local row translation to be performed separately at every copy of
a descendant word, without altering the other blocks. -/
theorem script_flatMap {ι : Type v} (indices : List ι)
    (f g : ι → List α) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, EditScript (f i) (g i) (cost i)) :
    EditScript (indices.flatMap f) (indices.flatMap g)
      ((indices.map cost).sum) := by
  induction indices with
  | nil => exact EditScript.nil []
  | cons i indices ih =>
      have hi := h i List.mem_cons_self
      have ht : ∀ j ∈ indices, EditScript (f j) (g j) (cost j) := by
        intro j hj
        exact h j (List.mem_cons_of_mem i hj)
      simpa only [List.flatMap_cons, List.map_cons, List.sum_cons] using
        script_trans (script_suffix (indices.flatMap f) hi)
          (script_prefix (g i) (ih ht))

theorem editDistance_flatMap_le_cost {ι : Type v} (indices : List ι)
    (f g : ι → List α) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, EditScript (f i) (g i) (cost i)) :
    ed (indices.flatMap f) (indices.flatMap g) ≤
      (indices.map cost).sum :=
  editDistance_le_script (script_flatMap indices f g cost h)

end TreeEdit.BinaryLower.CheapTranslations

end OAI
