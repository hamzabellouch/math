import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Init

namespace OAI

/-!
# Ordered trees with finite nonempty levels

The parent maps are monotone surjections. Thus every node has children,
and the children of consecutive parents occur in consecutive groups.
Ancestor maps are actual finite composites of parent maps.
-/

namespace ReflexiveFixedPoints

structure OrderedTree where
  size : ℕ → ℕ
  size_pos : ∀ k, 0 < size k
  size_zero : size 0 = 1
  parent : ∀ k, Fin (size (k + 1)) → Fin (size k)
  parent_monotone : ∀ k, Monotone (parent k)
  parent_surjective : ∀ k, Function.Surjective (parent k)

namespace OrderedTree

abbrev Node (T : OrderedTree) (k : ℕ) := Fin (T.size k)

variable (T : OrderedTree)

def root : T.Node 0 := ⟨0, T.size_pos 0⟩

theorem eq_root (v : T.Node 0) : v = T.root := by
  apply Fin.ext
  have hv : v.val < 1 := T.size_zero ▸ v.isLt
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hv)

/-- The ancestor at an earlier level, obtained by composing parent maps. -/
def ancestorLE {i j : ℕ} (h : i ≤ j) : T.Node j → T.Node i :=
  Nat.leRec (motive := fun k _ => T.Node k → T.Node i)
    id (fun {k} _ f => f ∘ T.parent k) h

@[simp] theorem ancestorLE_refl (i : ℕ) :
    T.ancestorLE (Nat.le_refl i) = id := by
  simp [ancestorLE]

theorem ancestorLE_step {i j : ℕ} (h : i ≤ j) :
    T.ancestorLE (Nat.le_succ_of_le h) = T.ancestorLE h ∘ T.parent j := by
  exact Nat.leRec_succ _ _ h

@[simp] theorem ancestorLE_succ (i : ℕ) :
    T.ancestorLE (Nat.le_succ i) = T.parent i := by
  rw [T.ancestorLE_step (Nat.le_refl i), T.ancestorLE_refl]
  rfl

theorem ancestorLE_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    T.ancestorLE (Nat.le_trans hij hjk) =
      T.ancestorLE hij ∘ T.ancestorLE hjk := by
  induction hjk using Nat.leRec with
  | refl => simp
  | @le_succ_of_le k h ih =>
      rw [T.ancestorLE_step (Nat.le_trans hij h), T.ancestorLE_step h, ih]
      rfl

@[simp] theorem ancestorLE_refl_apply (i : ℕ) (v : T.Node i) :
    T.ancestorLE (Nat.le_refl i) v = v := by
  rw [T.ancestorLE_refl]
  rfl

theorem ancestorLE_step_apply {i j : ℕ} (h : i ≤ j) (v : T.Node (j + 1)) :
    T.ancestorLE (Nat.le_succ_of_le h) v = T.ancestorLE h (T.parent j v) := by
  rw [T.ancestorLE_step h]
  rfl

@[simp] theorem ancestorLE_succ_apply (i : ℕ) (v : T.Node (i + 1)) :
    T.ancestorLE (Nat.le_succ i) v = T.parent i v := by
  rw [T.ancestorLE_succ]

theorem ancestorLE_trans_apply {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (v : T.Node k) :
    T.ancestorLE (Nat.le_trans hij hjk) v =
      T.ancestorLE hij (T.ancestorLE hjk v) := by
  rw [T.ancestorLE_trans hij hjk]
  rfl

theorem ancestorLE_monotone {i j : ℕ} (h : i ≤ j) :
    Monotone (T.ancestorLE h) := by
  induction h using Nat.leRec with
  | refl => simpa using (monotone_id : Monotone (id : T.Node i → T.Node i))
  | @le_succ_of_le j h ih =>
      rw [T.ancestorLE_step h]
      exact ih.comp (T.parent_monotone j)

theorem ancestorLE_surjective {i j : ℕ} (h : i ≤ j) :
    Function.Surjective (T.ancestorLE h) := by
  induction h using Nat.leRec with
  | refl =>
      intro v
      exact ⟨v, by simp⟩
  | @le_succ_of_le j h ih =>
      rw [T.ancestorLE_step h]
      exact ih.comp (T.parent_surjective j)

/-- The later-level descendants of a node. -/
def descendants {i j : ℕ} (h : i ≤ j) (v : T.Node i) : Finset (T.Node j) :=
  Finset.univ.filter (fun s => T.ancestorLE h s = v)

@[simp] theorem mem_descendants {i j : ℕ} (h : i ≤ j) (v : T.Node i)
    (s : T.Node j) :
    s ∈ T.descendants h v ↔ T.ancestorLE h s = v := by
  simp [descendants]

theorem descendants_nonempty {i j : ℕ} (h : i ≤ j) (v : T.Node i) :
    (T.descendants h v).Nonempty := by
  obtain ⟨s, hs⟩ := T.ancestorLE_surjective h v
  exact ⟨s, (T.mem_descendants h v s).2 hs⟩

/-- Every node between two descendants of the same node is a descendant. -/
theorem ancestorLE_eq_of_between {i j : ℕ} (h : i ≤ j) (v : T.Node i)
    {a b c : T.Node j} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : T.ancestorLE h a = v) (hc : T.ancestorLE h c = v) :
    T.ancestorLE h b = v := by
  apply le_antisymm
  · simpa only [hc] using T.ancestorLE_monotone h hbc
  · simpa only [ha] using T.ancestorLE_monotone h hab

theorem mem_descendants_of_between {i j : ℕ} (h : i ≤ j) (v : T.Node i)
    {a b c : T.Node j} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : a ∈ T.descendants h v) (hc : c ∈ T.descendants h v) :
    b ∈ T.descendants h v := by
  apply (T.mem_descendants h v b).2
  exact T.ancestorLE_eq_of_between h v hab hbc
    ((T.mem_descendants h v a).1 ha) ((T.mem_descendants h v c).1 hc)

end OrderedTree
end ReflexiveFixedPoints

end OAI
