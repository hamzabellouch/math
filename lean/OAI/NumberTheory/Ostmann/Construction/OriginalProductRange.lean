import OAI.NumberTheory.Ostmann.Construction.WordRootRange

namespace OAI

/-! # Root cutoffs for the product of specified original prime coordinates -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def originalProductRange {V : Type*} (w : List V) (n : ℕ) (lo hi : ℝ) :
    WordRange (ExpandedScheduledVariable V n) := ⟨w.map Sum.inl, lo, hi⟩

theorem originalProductRange_holds {V : Type*} (w : List V) (n : ℕ) (lo hi : ℝ) (x : V → ℕ) :
    ((originalProductRange w n lo hi).toHistory .prime).Holds
        (expandedPrimeValues n (fun i => (x i : ℤ))) ↔
      lo ≤ ((w.map x).prod : ℝ) ∧ ((w.map x).prod : ℝ) ≤ hi := by
  have he := WordRange.toHistory_holds (originalProductRange w n lo hi) .prime
    (expandedPrimeValues n (fun i => (x i : ℤ))) (expandedPrimeNatValues n x)
    (by
      intro i
      cases i <;> simp only [HistoryFormula.value_prime, expandedPrimeValues,
        expandedPrimeNatValues, Int.cast_natCast, Int.cast_one, Nat.cast_one])
  rw [he]
  simp only [WordRange.Holds, originalProductRange, List.map_map, Function.comp_def,
    expandedPrimeNatValues, Set.mem_Icc]

theorem primeUnitRangedCoefficient_originalProductRange {V : Type*} {n : ℕ}
    (f : WordFourierParameters n) (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (w : List V) (lo hi : ℝ)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    f.primeUnitRangedCoefficient C U (D.prependRoot (originalProductRange w n lo hi)) template t ht x =
      if lo ≤ ((w.map x).prod : ℝ) ∧ ((w.map x).prod : ℝ) ≤ hi then
        f.primeUnitRangedCoefficient C U D template t ht x else 0 := by
  simpa only [originalProductRange_holds] using
    f.primeUnitRangedCoefficient_prependRoot C U D (originalProductRange w n lo hi) template t ht x

end Ostmann

end OAI
