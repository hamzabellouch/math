import OAI.NumberTheory.Ostmann.Arithmetic.SplitPrefixProducts
import OAI.NumberTheory.Ostmann.Characters.TreeSplitCoordinates

namespace OAI

/-! # The checked split-coordinate equivalence records actual product splits -/

namespace Ostmann

@[implicit_reducible] def splitSampleList {G : Type} : (n : ℕ) → SplitSamples G n → List G
  | 0, _ => []
  | n + 1, x => x.1 :: splitSampleList n x.2

theorem splitSampleList_cast_symm {G A : Type} (m n : ℕ) (h : m = n)
    (e : SplitSamples G m ≃ A) (he : (SplitSamples G n ≃ A) = (SplitSamples G m ≃ A)) (x : A) :
    splitSampleList n ((he.mpr e).symm x) = splitSampleList m (e.symm x) := by
  cases h
  rfl

theorem splitSampleList_cast_apply {G A : Type} (m n : ℕ) (h : m = n)
    (e : A ≃ SplitSamples G m) (he : (A ≃ SplitSamples G n) = (A ≃ SplitSamples G m)) (x : A) :
    splitSampleList n ((he.mpr e) x) = splitSampleList m (e x) := by
  cases h
  rfl

theorem splitSampleList_append {G : Type} (m n : ℕ)
    (x : SplitSamples G m) (y : SplitSamples G n) :
    splitSampleList (m + n) ((splitSamplesAppendEquiv G m n).symm (x, y)) =
      splitSampleList m x ++ splitSampleList n y := by
  induction m with
  | zero =>
    simp only [splitSamplesAppendEquiv]
    rw [splitSampleList_cast_symm n (0 + n) (Nat.zero_add n).symm]
    rfl
  | succ m ih =>
    simp only [splitSamplesAppendEquiv]
    rw [splitSampleList_cast_symm (m + n + 1) (m + 1 + n) (by omega)]
    change x.1 :: splitSampleList (m + n) ((splitSamplesAppendEquiv G m n).symm (x.2, y)) =
      (x.1 :: splitSampleList m x.2) ++ splitSampleList n y
    rw [ih]
    rfl

theorem splitSampleList_treeLeafSplit {G : Type} [CommGroup G]
    (n : ℕ) (P : G) (x : TreeLeafFiber G n P) :
    splitSampleList (2 ^ n - 1) (treeLeafSplitEquiv n P x) = actualSplitValues n x.1 := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    have hn : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have he : (2 ^ n - 1) + (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
      rw [pow_succ]
      omega
    simp only [treeLeafSplitEquiv]
    rw [splitSampleList_cast_apply _ _ he]
    change treeLeafProduct n x.1.1 ::
      splitSampleList ((2 ^ n - 1) + (2 ^ n - 1))
        ((splitSamplesAppendEquiv G (2 ^ n - 1) (2 ^ n - 1)).symm
          (treeLeafSplitEquiv n (treeLeafProduct n x.1.1) ⟨x.1.1, rfl⟩,
           treeLeafSplitEquiv n (P / treeLeafProduct n x.1.1) ⟨x.1.2, _⟩)) = _
    rw [splitSampleList_append, ih, ih]
    rfl

/-- Each parent recorded by the actual split-coordinate equivalence is
computed from the preceding coordinates, including in right subtrees. -/
theorem split_coordinate_parent {G : Type} [CommGroup G]
    (n : ℕ) (P : G) (x : TreeLeafFiber G n P) (j : ℕ) (hj : j < 2 ^ n - 1) :
    (actualParentSplits n x.1).getD j (1, 1) =
      (splitPrefixParent n P
        ((splitSampleList (2 ^ n - 1) (treeLeafSplitEquiv n P x)).take j).reverse,
        (splitSampleList (2 ^ n - 1) (treeLeafSplitEquiv n P x)).getD j 1) := by
  rw [splitSampleList_treeLeafSplit]
  have h := actualParentSplits_from_prefix n x.1 j hj
  simpa only [x.property] using h

end Ostmann

end OAI
