import OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordIdentity

namespace OAI

/-! Identify the scalar word expectations appearing in the matrix bound. -/

namespace TwoPointCorrelations

open scoped Classical

theorem maskedClosedWord_residue_average {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (s budget : ℕ) (hR : 0 < R) (hRD : R ≤ budget)
    (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (hg : ∀ n, g n ≠ 0) :
    (data.residueLaw B hB).average (fun x => scalarWalkProduct h
      (maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
        L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n))
      (data.residueOrigin x) (columnTupleWord w forward padding)) =
      prohibitedCenteredAverage data hB s budget (columnTupleWord w forward padding) label
        (data.residueValue (fun n => scalarWalkProduct h
          (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K
            (fun t => extra t.tuple) h) n (columnTupleWord w forward padding))) := by
  have hw : maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n) =
      fun t n =>
        (if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then (0 : ℝ) else 1) *
          signedIntegerWeight Q u (eligible t.tuple) g (centeredTuple t.tuple.primeFactors)
            L K (extra t.tuple) h t n *
          (if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + t.displacement h)
            then (0 : ℝ) else 1) := by
    funext t n
    by_cases hn : ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n <;>
      by_cases hm : ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
        (n + t.displacement h) <;>
      simp [maskedSignedIntegerWeight, vertexIndicator, hn, hm]
  rw [hw]
  exact closed_masked_word_average data hB w forward padding hprime hdisjoint label hlabel
    s budget hR hRD hclosed Q u (fun t => eligible t.tuple) g L K
    (fun t => extra t.tuple) hg

end TwoPointCorrelations

end OAI
