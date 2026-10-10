import OAI.NumberTheory.Ostmann.Construction.PrimeWordCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.RangedExpandedWordPairBound

namespace OAI

/-! # Adding one exact product cutoff at the root of a history -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def WordRangeDecoration.prependRoot {σ : Type*} (r : WordRange σ) :
    {n : ℕ} → WordRangeDecoration σ n → WordRangeDecoration σ n
  | 0, .leaf ranges => .leaf (r :: ranges)
  | _ + 1, .node ranges L R => .node (r :: ranges) L R

theorem WordRangeDecoration.prependRoot_count {σ : Type*} {n : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n) :
    (D.prependRoot r).count = D.count + 1 := by
  cases D with
  | leaf ranges => simp only [prependRoot, count, List.length_cons]
  | node ranges L R => simp only [prependRoot, count, List.length_cons]; omega

theorem WordRangeDecoration.prependRoot_bounded {σ : Type*} {n B : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n)
    (hr : r.word.length + 1 ≤ B) (hD : D.WordsBounded B) :
    (D.prependRoot r).WordsBounded B := by
  cases D with
  | leaf ranges =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hr
    · exact hD q hq
  | node ranges L R =>
    refine ⟨?_, hD.2.1, hD.2.2⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hr
    · exact hD.1 q hq

theorem WordRangeDecoration.prependRoot_formulas {σ : Type*} {n : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.prependRoot r).formulas template t ht env =
      r.toHistory env :: D.formulas template t ht env := by
  cases template <;> cases D <;> rfl

theorem WordFourierParameters.primeUnitRangedCoefficient_prependRoot {V : Type*} {n : ℕ}
    (f : WordFourierParameters n) (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (r : WordRange (ExpandedScheduledVariable V n))
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    f.primeUnitRangedCoefficient C U (D.prependRoot r) template t ht x =
      (if (r.toHistory .prime).Holds (expandedPrimeValues n (fun i => (x i : ℤ))) then
        f.primeUnitRangedCoefficient C U D template t ht x else 0) := by
  simp only [primeUnitRangedCoefficient, unitRangedCoefficient, rangedCoefficient,
    WordRangeDecoration.prependRoot_formulas, List.forall_mem_cons]
  split_ifs <;> simp_all

/-- The finite correlation bound uses only the number of range tests, not
its endpoints. Thus the same bound applies uniformly to every root cutoff. -/
theorem rangedWordTransferPairBound_root_endpoints {σ : Type*} {n : ℕ}
    (template template' : WordTransferTemplate σ n) (D D' : WordRangeDecoration σ n)
    (r r' : WordRange σ) (t t' : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (f f' : WordFourierParameters n) (A E : ℕ)
    (P Q : Finset ℕ) (lower : ℝ) (Bq : ℕ) :
    rangedWordTransferPairBound template template' (D.prependRoot r) D' t t' ht ht' B f f' A E P Q lower Bq =
      rangedWordTransferPairBound template template' (D.prependRoot r') D' t t' ht ht' B f f' A E P Q lower Bq := by
  simp only [rangedWordTransferPairBound, WordRangeDecoration.prependRoot_count]

end Ostmann

end OAI
