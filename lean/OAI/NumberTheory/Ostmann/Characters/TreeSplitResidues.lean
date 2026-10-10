import Mathlib.Data.List.GetD
import OAI.NumberTheory.Ostmann.Arithmetic.SplitSampleLists
import OAI.NumberTheory.Ostmann.Characters.TreeTupleProfiles

namespace OAI

/-! # Integer bulk products and their exposed unit residues -/

namespace Ostmann

/-- Both actual child products, in the same preorder as the frequencies. -/
def actualChildProducts {G : Type*} [CommMonoid G] : (n : ℕ) → TreeLeafTuple G n → List (G × G)
  | 0, _ => []
  | n + 1, x => (treeLeafProduct n x.1, treeLeafProduct n x.2) ::
      (actualChildProducts n x.1 ++ actualChildProducts n x.2)

theorem actualChildProducts_length {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafTuple G n) : (actualChildProducts n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [actualChildProducts, List.length_cons, List.length_append, ih]
    have := Nat.one_le_two_pow (n := n)
    rw [pow_succ]
    omega

theorem actualParentSplits_childProducts {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafTuple G n) :
    actualParentSplits n x = (actualChildProducts n x).map (fun a => (a.1 * a.2, a.1)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [actualParentSplits, actualChildProducts, List.map_cons,
      List.map_append, ih, treeLeafProduct]

theorem actualChildProducts_from_prefix {G : Type} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (j : ℕ) (hj : j < 2 ^ n - 1) :
    (actualChildProducts n x).getD j (1, 1) =
      ((actualSplitValues n x).getD j 1,
        splitPrefixParent n (treeLeafProduct n x) ((actualSplitValues n x).take j).reverse /
          (actualSplitValues n x).getD j 1) := by
  have h := actualParentSplits_from_prefix n x j hj
  rw [actualParentSplits_childProducts] at h
  have hm := List.getD_map (actualChildProducts n x) (1, 1)
    (n := j) (fun a => (a.1 * a.2, a.1))
  simp only [one_mul] at hm
  rw [hm] at h
  change (((actualChildProducts n x).getD j (1, 1)).1 *
    ((actualChildProducts n x).getD j (1, 1)).2,
    ((actualChildProducts n x).getD j (1, 1)).1) = _ at h
  have hL := congrArg Prod.snd h
  have hP := congrArg Prod.fst h
  dsimp only at hL hP
  apply Prod.ext hL
  change ((actualChildProducts n x).getD j (1, 1)).2 =
    splitPrefixParent n (treeLeafProduct n x) ((actualSplitValues n x).take j).reverse /
      (actualSplitValues n x).getD j 1
  rw [← hL, ← hP, mul_div_cancel_left]

/-- Equality of all leaf residues, expressed on the original binary tuple. -/
def treeIntegerResidues (Q : ℕ) : (n : ℕ) → TreeLeafTuple ℤ n →
    TreeLeafTuple (ZMod Q)ˣ n → Prop
  | 0, a, u => Units.val (show (ZMod Q)ˣ from u) = ((show ℤ from a) : ZMod Q)
  | n + 1, a, u => treeIntegerResidues Q n a.1 u.1 ∧ treeIntegerResidues Q n a.2 u.2

theorem treeIntegerResidues_product (Q n : ℕ) (a : TreeLeafTuple ℤ n)
    (u : TreeLeafTuple (ZMod Q)ˣ n) (h : treeIntegerResidues Q n a u) :
    ((treeLeafProduct n u : (ZMod Q)ˣ) : ZMod Q) = treeLeafProduct n a := by
  induction n with
  | zero => exact h
  | succ n ih =>
    change ((treeLeafProduct n u.1 * treeLeafProduct n u.2 : (ZMod Q)ˣ) : ZMod Q) = _
    rw [Units.val_mul, ih _ _ h.1, ih _ _ h.2]
    exact (Int.cast_mul _ _).symm

theorem treeIntegerResidues_children (Q n : ℕ) (a : TreeLeafTuple ℤ n)
    (u : TreeLeafTuple (ZMod Q)ˣ n) (h : treeIntegerResidues Q n a u) :
    (actualChildProducts n u).map (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q))) =
      (actualChildProducts n a).map (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [actualChildProducts, List.map_cons, List.map_append,
      treeIntegerResidues_product Q n _ _ h.1, treeIntegerResidues_product Q n _ _ h.2,
      ih _ _ h.1, ih _ _ h.2]

theorem treeIntegerResidues_child (Q n : ℕ) (a : TreeLeafTuple ℤ n)
    (u : TreeLeafTuple (ZMod Q)ˣ n) (h : treeIntegerResidues Q n a u) (j : ℕ) :
    (((actualChildProducts n u).getD j (1, 1)).1 : ZMod Q) =
        ((actualChildProducts n a).getD j (1, 1)).1 ∧
    (((actualChildProducts n u).getD j (1, 1)).2 : ZMod Q) =
        ((actualChildProducts n a).getD j (1, 1)).2 := by
  have he := congrArg (fun l => l.getD j ((1 : ZMod Q), 1))
    (treeIntegerResidues_children Q n a u h)
  have hu := List.getD_map (actualChildProducts n u) (1, 1) (n := j)
    (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q)))
  have ha := List.getD_map (actualChildProducts n a) (1, 1) (n := j)
    (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q)))
  simp only [Units.val_one] at hu
  simp only [Int.cast_one] at ha
  rw [hu, ha] at he
  exact Prod.mk.inj he

/-- Agreement of the total and the exposed prefix fixes both child-product
residues at every earlier node, including nodes in right subtrees. -/
theorem exposed_prefix_children_eq {G : Type} [CommGroup G]
    (n : ℕ) (u v : TreeLeafTuple G n) (j : ℕ)
    (htotal : treeLeafProduct n u = treeLeafProduct n v)
    (hpast : (actualSplitValues n u).take j = (actualSplitValues n v).take j)
    (i : ℕ) (hi : i < j) (hj : j ≤ 2 ^ n - 1) :
    (actualChildProducts n u).getD i (1, 1) = (actualChildProducts n v).getD i (1, 1) := by
  have htake : (actualSplitValues n u).take i = (actualSplitValues n v).take i := by
    have ht := congrArg (List.take i) hpast
    simpa only [List.take_take, min_eq_left (Nat.le_of_lt hi)] using ht
  have hget : (actualSplitValues n u).getD i 1 = (actualSplitValues n v).getD i 1 := by
    have he := congrArg (fun l => l.getD i 1) hpast
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi] using he
  rw [actualChildProducts_from_prefix n u i (by omega),
    actualChildProducts_from_prefix n v i (by omega), htotal, htake, hget]

end Ostmann

end OAI
