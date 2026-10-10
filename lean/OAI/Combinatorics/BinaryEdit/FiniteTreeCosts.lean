import OAI.Combinatorics.BinaryEdit.FiniteTreeWords
import OAI.Combinatorics.BinaryEdit.CheapTranslations

namespace OAI

/-!
# Inexpensive scripts in the recursive row evaluator

Local row advancement and descendant-occurrence lifting establish
`lem:finite-cost` from geometric hypotheses on state translations and
invisible leaf decoders.
-/

namespace TreeEdit.BinaryLower.FiniteTree

open CheapTranslations

variable {A Γ : Type*} [AddCommMonoid A]

theorem nodeWord_eq_orbitRows {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) :
    nodeWord T leaf u (h + 1) p x =
      orbitRows (nodeRow T leaf u h p) x (u p) T := by
  simp only [nodeWord, orbitRows, rowWindow, nodeRow, List.range_eq_range']

/-- Advancing the rows in one node has exactly the source's deletion/insertion
script cost, uniformly in its state (including all ancestor offsets). -/
theorem nodeWord_cheap_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) (s : ℕ) (hs : s ≤ T) :
    EditScript (nodeWord T leaf u (h + 1) p x)
      (nodeWord T leaf u (h + 1) p (x + s • u p))
      (2 * s * m * (m * T) ^ h) := by
  rw [nodeWord_eq_orbitRows, nodeWord_eq_orbitRows]
  simpa only [Nat.mul_assoc] using
    script_orbitRows_shift (nodeRow T leaf u h p) x (u p) T s
      (m * (m * T) ^ h) hs (nodeRow_length T leaf u h p)

theorem nodeWord_cheap_editDistance {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) (s : ℕ) (hs : s ≤ T) :
    ed (nodeWord T leaf u (h + 1) p x)
      (nodeWord T leaf u (h + 1) p (x + s • u p)) ≤
      2 * s * m * (m * T) ^ h :=
  editDistance_le_script (nodeWord_cheap_script T leaf u h p x s hs)

/-- A uniform script at one descendant lifts through its `T^q.length`
occurrences. Leaf decoders outside that descendant must be invariant under
the same state translation. Every intermediate word remains unrestricted. -/
theorem nodeWord_descendant_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (z : A) (C : ℕ)
    (hlocal : ∀ y, EditScript (nodeWord T leaf u h (p ++ q) y)
      (nodeWord T leaf u h (p ++ q) (y + z)) C)
    (houtside : ∀ r : List (Fin m), r.length = h + q.length →
      ¬ q.IsPrefix r → ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y)
    (x : A) :
    EditScript (nodeWord T leaf u (h + q.length) p x)
      (nodeWord T leaf u (h + q.length) p (x + z)) (T ^ q.length * C) := by
  classical
  induction q generalizing p x with
  | nil => simpa using hlocal x
  | cons i q ih =>
      have htarget (y : A) :
          EditScript (nodeWord T leaf u (h + q.length) (p ++ [i]) y)
            (nodeWord T leaf u (h + q.length) (p ++ [i]) (y + z))
            (T ^ q.length * C) := by
        apply ih (p := p ++ [i]) (x := y)
        · intro v
          simpa only [List.append_assoc, List.singleton_append] using hlocal v
        · intro r hr hn v
          have hlen : (i :: r).length = h + (i :: q).length := by
            simp only [List.length_cons, hr]
            omega
          have hnot : ¬ (i :: q).IsPrefix (i :: r) := by
            simpa only [List.cons_prefix_cons, true_and] using hn
          simpa only [List.append_assoc, List.singleton_append] using
            houtside (i :: r) hlen hnot v
      have hchild (a : ℕ) (j : Fin m) :
          EditScript
            (nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
            (nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
            (if j = i then T ^ q.length * C else 0) := by
        rw [add_right_comm x z]
        by_cases hji : j = i
        · subst j
          simpa only [ite_true] using htarget (x + a • u p)
        · simp only [ite_eq_right hji]
          have hinv : ∀ r : List (Fin m), r.length = h + q.length → ∀ y,
              leaf ((p ++ [j]) ++ r) (y + z) = leaf ((p ++ [j]) ++ r) y := by
            intro r hr y
            have hlen : (j :: r).length = h + (i :: q).length := by
              simp only [List.length_cons, hr]
              omega
            have hnot : ¬ (i :: q).IsPrefix (j :: r) := by
              simp only [List.cons_prefix_cons, Ne.symm hji, false_and, not_false_eq_true]
            simpa only [List.append_assoc, List.singleton_append] using
              houtside (j :: r) hlen hnot y
          rw [nodeWord_invariant T leaf u (h + q.length) (p ++ [j]) z hinv]
          exact EditScript.nil _
      have hrow (a : ℕ) :
          EditScript
            ((List.finRange m).flatMap fun j =>
              nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
            ((List.finRange m).flatMap fun j =>
              nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
            (T ^ q.length * C) := by
        have hs := script_flatMap (List.finRange m)
          (fun j => nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
          (fun j => nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
          (fun j => if j = i then T ^ q.length * C else 0)
          (fun j _ => hchild a j)
        simpa [List.finRange, List.sum_ofFn, Function.comp_def] using hs
      have hs := script_flatMap (List.range T)
        (fun a => (List.finRange m).flatMap fun j =>
          nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
        (fun a => (List.finRange m).flatMap fun j =>
          nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
        (fun _ => T ^ q.length * C) (fun a _ => hrow a)
      simpa [nodeWord, Nat.add_assoc, pow_succ, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hs

/-- Changing only one leaf decoder costs one substitution in each of its
`T^q.length` occurrences, irrespective of how much its state changes. -/
theorem nodeWord_leaf_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (q p : List (Fin m)) (z : A)
    (houtside : ∀ r : List (Fin m), r.length = q.length → r ≠ q →
      ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y)
    (x : A) :
    EditScript (nodeWord T leaf u q.length p x)
      (nodeWord T leaf u q.length p (x + z)) (T ^ q.length) := by
  have hlocal : ∀ y, EditScript (nodeWord T leaf u 0 (p ++ q) y)
      (nodeWord T leaf u 0 (p ++ q) (y + z)) 1 := by
    intro y
    exact EditScript.cons
      (EditStep.substitute [] [] (leaf (p ++ q) y) (leaf (p ++ q) (y + z)))
      (EditScript.nil _)
  have hout : ∀ r : List (Fin m), r.length = 0 + q.length →
      ¬ q.IsPrefix r → ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y := by
    intro r hr hn y
    apply houtside r (by simpa using hr) _ y
    intro heq
    subst r
    exact hn List.prefix_rfl
  simpa using nodeWord_descendant_script T leaf u 0 q p z 1 hlocal hout x

theorem nodeWord_leaf_editDistance {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (q p : List (Fin m)) (z : A)
    (houtside : ∀ r : List (Fin m), r.length = q.length → r ≠ q →
      ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y)
    (x : A) :
    ed (nodeWord T leaf u q.length p x)
      (nodeWord T leaf u q.length p (x + z)) ≤ T ^ q.length :=
  editDistance_le_script (nodeWord_leaf_script T leaf u q p z houtside x)

/-- Combined local row advancement and occurrence lifting, with exactly the
cost `T^depth * 2*s*rowLength` used in the finite-tree construction. -/
theorem nodeWord_descendant_cheap_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (s : ℕ) (hs : s ≤ T)
    (houtside : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leaf (p ++ r) (y + s • u (p ++ q)) = leaf (p ++ r) y)
    (x : A) :
    EditScript (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q)))
      (T ^ q.length * (2 * s * m * (m * T) ^ h)) :=
  nodeWord_descendant_script T leaf u (h + 1) q p (s • u (p ++ q))
    (2 * s * m * (m * T) ^ h)
    (fun y => nodeWord_cheap_script T leaf u h (p ++ q) y s hs) houtside x

theorem nodeWord_descendant_cheap_editDistance {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (s : ℕ) (hs : s ≤ T)
    (houtside : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leaf (p ++ r) (y + s • u (p ++ q)) = leaf (p ++ r) y)
    (x : A) :
    ed (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q))) ≤
      T ^ q.length * (2 * s * m * (m * T) ^ h) :=
  editDistance_le_script
    (nodeWord_descendant_cheap_script T leaf u h q p s hs houtside x)

/-- The pointwise leaf-cost estimate in the manuscript's normalized form,
with `M = (mT)^q.length`. -/
theorem nodeWord_leaf_normalized_bound {m : ℕ} (T : ℕ) (hm : 0 < m)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (q p : List (Fin m)) (z : A)
    (houtside : ∀ r : List (Fin m), r.length = q.length → r ≠ q →
      ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y)
    (x : A) :
    (ed (nodeWord T leaf u q.length p x)
      (nodeWord T leaf u q.length p (x + z)) : ℝ) ≤
      ((m * T : ℕ) : ℝ) ^ q.length / (m : ℝ) ^ q.length := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hb := nodeWord_leaf_editDistance T leaf u q p z houtside x
  have hn : (ed (nodeWord T leaf u q.length p x)
      (nodeWord T leaf u q.length p (x + z)) : ℝ) ≤ (T : ℝ) ^ q.length := by
    exact_mod_cast hb
  simpa only [Nat.cast_mul, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hm0)]
    using hn

/-- Equation `eq:finite-cost` for the recursive word evaluator: a depth-j
translation by s cheap node steps costs at most `(2s/T) M/m^j`.
The decoder-locality hypothesis is exactly what makes other subtrees unchanged. -/
theorem nodeWord_descendant_normalized_bound {m : ℕ} (T : ℕ)
    (hm : 0 < m) (hT : 0 < T)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (s : ℕ) (hs : s ≤ T)
    (houtside : ∀ r : List (Fin m), r.length = h + 1 + q.length →
      ¬ q.IsPrefix r → ∀ y,
        leaf (p ++ r) (y + s • u (p ++ q)) = leaf (p ++ r) y)
    (x : A) :
    (ed (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q))) : ℝ) ≤
      (2 * (s : ℝ) / T) *
        (((m * T : ℕ) : ℝ) ^ (h + 1 + q.length) / (m : ℝ) ^ q.length) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hb := nodeWord_descendant_cheap_editDistance T leaf u h q p s hs houtside x
  have hn : (ed (nodeWord T leaf u (h + 1 + q.length) p x)
      (nodeWord T leaf u (h + 1 + q.length) p (x + s • u (p ++ q))) : ℝ) ≤
      (T : ℝ) ^ q.length * (2 * (s : ℝ) * m * ((m : ℝ) * T) ^ h) := by
    exact_mod_cast hb
  calc
    _ ≤ (T : ℝ) ^ q.length * (2 * (s : ℝ) * m * ((m : ℝ) * T) ^ h) := hn
    _ = _ := by
      simp only [Nat.cast_mul, pow_add, pow_one, mul_pow]
      field_simp

end TreeEdit.BinaryLower.FiniteTree

end OAI
