import OAI.Combinatorics.BinaryEdit.FiniteTreeGeometry

namespace OAI

/-!
# Concrete tagged alphabets below finite-tree nodes

The generic row lemma needs disjoint alphabets for distinct children. Here
that hypothesis is proved for the actual tagged cyclic-state symbols, not
postulated as an additional property of the construction.
-/

namespace TreeEdit.BinaryLower.FiniteTree

/-- Every symbol in a genuine subtree word retains a leaf extending its prefix. -/
theorem symbol_prefix_of_mem {m k T : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State Q) (s : Symbol Q)
    (hs : s ∈ nodeWord T (leafDecoder Q base) u h p x) : p <+: s.1.val := by
  induction h generalizing p x with
  | zero =>
      have hp : p.length = k := by simpa using hlen
      simp only [nodeWord, List.mem_singleton] at hs
      subst s
      rw [leafDecoder_of_length Q base p hp x]
  | succ h ih =>
      simp only [nodeWord, List.mem_flatMap] at hs
      obtain ⟨a, ha, i, hi, hmem⟩ := hs
      have hlenChild : (p ++ [i]).length + h = k := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hchild := ih (p ++ [i]) hlenChild (x + a • u p) hmem
      exact (List.prefix_append p [i]).trans hchild

/-- The actual alphabet below a prefix consists of tagged leaf residues. -/
def subtreeAlphabet {m k : ℕ} (Q : Leaf m k → ℕ) (p : List (Fin m)) :
    Set (Symbol Q) := {s | p <+: s.1.val}

lemma mem_subtreeAlphabet_of_mem {m k T : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State Q) (s : Symbol Q)
    (hs : s ∈ nodeWord T (leafDecoder Q base) u h p x) :
    s ∈ subtreeAlphabet Q p := symbol_prefix_of_mem Q base u h p hlen x s hs

lemma child_eq_of_prefixes {α : Type*} (p l : List α) (i j : α)
    (hi : p ++ [i] <+: l) (hj : p ++ [j] <+: l) : i = j := by
  have he : p ++ [i] = p ++ [j] := by
    calc
      p ++ [i] = l.take (p ++ [i]).length := List.prefix_iff_eq_take.mp hi
      _ = l.take (p ++ [j]).length := by simp
      _ = p ++ [j] := (List.prefix_iff_eq_take.mp hj).symm
  simpa using List.append_cancel_left he

/-- Immediate child alphabets are pairwise disjoint, uniformly in all states. -/
theorem subtreeAlphabet_children_pairwise_disjoint {m k : ℕ}
    (Q : Leaf m k → ℕ) (p : List (Fin m)) :
    Pairwise fun i j : Fin m =>
      Disjoint (subtreeAlphabet Q (p ++ [i])) (subtreeAlphabet Q (p ++ [j])) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro s hi hj
  exact hij (child_eq_of_prefixes p s.1.val i j hi hj)

/-- In particular equal symbols in two child words force equal child indices,
with no requirement that the states at the two occurrences coincide. -/
theorem child_index_eq_of_common_symbol {m k T h : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (p : List (Fin m)) (hlen : p.length + (h + 1) = k)
    (i j : Fin m) (x y : State Q) (s : Symbol Q)
    (hi : s ∈ nodeWord T (leafDecoder Q base) u h (p ++ [i]) x)
    (hj : s ∈ nodeWord T (leafDecoder Q base) u h (p ++ [j]) y) : i = j := by
  apply child_eq_of_prefixes p s.1.val i j
  · exact symbol_prefix_of_mem Q base u h (p ++ [i])
      (by simp only [List.length_append, List.length_singleton]; omega) x s hi
  · exact symbol_prefix_of_mem Q base u h (p ++ [j])
      (by simp only [List.length_append, List.length_singleton]; omega) y s hj

end TreeEdit.BinaryLower.FiniteTree

end OAI
