import OAI.NumberTheory.Ostmann.Arithmetic.SplitSampleLists
import OAI.NumberTheory.Ostmann.Arithmetic.SingleHistorySupport

namespace OAI

/-! # Passing all actual preorder node tests retains the whole support weight -/

namespace Ostmann

open scoped Classical

theorem sequentialSupport_eq_one_of_prefix {A : Type} [One A]
    (test : List A → A → Prop) (past : List A) (n : ℕ) (x : SplitSamples A n)
    (htest : ∀ j < n, test (((splitSampleList n x).take j).reverse ++ past)
      ((splitSampleList n x).getD j 1)) : sequentialSupport test past n x = 1 := by
  induction n generalizing past with
  | zero => rfl
  | succ n ih =>
    have h0 : test past x.1 := by simpa [splitSampleList] using htest 0 (by omega)
    change (if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0) = 1
    rw [ite_eq_left h0]
    apply ih
    intro j hj
    have ht := htest (j + 1) (by omega)
    simpa only [splitSampleList, List.take_succ_cons, List.reverse_cons,
      List.getD_cons_succ, List.append_assoc, List.singleton_append] using ht

/-- The support is evaluated on the original leaf tuple. Its tests are
checked at the actual parent/child product splits, in their true order. -/
theorem singleArithmeticLeafSupport_eq_one_of_actual_tests {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n)
    (htest : ∀ j < 2 ^ n - 1,
      singleArithmeticSplitTest
        (data (treeLeafProduct n x) (((actualSplitValues n x).take j).reverse))
        ((actualSplitValues n x).getD j 1)) :
    singleArithmeticLeafSupport n data x = 1 := by
  unfold singleArithmeticLeafSupport
  apply sequentialSupport_eq_one_of_prefix
  intro j hj
  simpa only [List.append_nil, splitSampleList_treeLeafSplit] using htest j hj

end Ostmann

end OAI
