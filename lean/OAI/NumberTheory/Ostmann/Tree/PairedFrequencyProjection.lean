import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveFrequencySupport

namespace OAI

/-! # The two actual frequency histories inside a paired tree -/

namespace Ostmann
open scoped Classical

def frequencyPairProjection (S : Finset ℤ) (n : ℕ) (b : Bool)
    (t : FrequencyTree (S × S) n) : FrequencyTree S n :=
  frequencyTreeMap (fun p => if b then p.2 else p.1) n t

theorem frequencySplitList_projection (S : Finset ℤ) (n : ℕ) (b : Bool)
    (t : FrequencyTree (S × S) n) :
    singleFrequencySplitList S n (frequencyPairProjection S n b t) =
      (frequencySplitList S n t).map (fun p => if b then p.2 else p.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl := ih t.2.1
    have hr := ih t.2.2
    dsimp only [frequencyPairProjection] at hl hr
    simp only [frequencyPairProjection, frequencyTreeMap, singleFrequencySplitList,
      frequencySplitList, List.map_cons, List.map_append, frequencyRoot_map,
      hl, hr]
    cases b <;> rfl

theorem treeNodeFrequencies_projection (S : Finset ℤ) (n : ℕ) (b : Bool)
    (t : FrequencyTree (S × S) n) (j : ℕ) :
    singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j =
      if b then (treeNodeFrequencies S n t j).2 else (treeNodeFrequencies S n t j).1 := by
  unfold singleTreeNodeFrequencies treeNodeFrequencies
  rw [frequencySplitList_projection]
  have h := List.getD_map (frequencySplitList S n t)
    (emptyNodeFrequencies, emptyNodeFrequencies) (fun p => if b then p.2 else p.1) (n := j)
  cases b <;> simpa only [Bool.false_eq_true, ite_false, ite_true] using h

end Ostmann

end OAI
