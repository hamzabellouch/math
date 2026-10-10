import OAI.NumberTheory.TwoPoint.Bounds.ResidueMatrixMoment
import OAI.NumberTheory.TwoPoint.Walks.ClosedTraceEncoding

namespace OAI

/-! Discharge residue periodicity for the literal prime-family matrix weights. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem primeClosedPair_residue_congr {h J M B k : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hP : ∀ j, P j ⊆ data.P) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (s : ℕ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool))
    (t : SignedStep)
    (ht : t ∈ integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b))
    (n m : ℤ) (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t n =
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t m := by
  rw [← closedTraceEncoding_word Q (a, b)] at ht
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  apply maskedSignedIntegerWeight_residue_congr data hB s Q u eligible g L K extra
    hsq hpool hg hextra _ _ n m hnm
  rw [columnTuple_primeFactors _ i hprime hdisjoint]
  intro p hp
  obtain ⟨j, _, rfl⟩ := mem_image.mp hp
  exact hP j ((closedTraceEncoding Q (a, b)).2.1 j i).property

lemma maskedSignedIntegerWeight_pairs (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (keep : ℤ → Prop)
    (pairs : Finset (ℕ × ℕ)) (hallowed : ∀ d q, eligible d q → (d, q) ∈ pairs)
    (t : SignedStep) (n : ℤ)
    (hw : maskedSignedIntegerWeight Q u eligible g center L K extra h keep t n ≠ 0) :
    (t.tuple, t.padding) ∈ pairs := by
  have hs := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2
  exact hallowed _ _ (signedIntegerWeight_nonzero Q u (eligible t.tuple) g
    (center t.tuple) L K (extra t.tuple) h t n hs).2.1

lemma scalarWalkProduct_pairs (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (pairs : Finset (ℕ × ℕ))
    (hsupport : ∀ t n, weight t n ≠ 0 → (t.tuple, t.padding) ∈ pairs)
    (w : List SignedStep) (n : ℤ) (hw : scalarWalkProduct h weight n w ≠ 0) :
    ∀ t ∈ w, (t.tuple, t.padding) ∈ pairs := by
  induction w generalizing n with
  | nil => simp
  | cons t w ih =>
      have hp := mul_ne_zero_iff.mp hw
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hsupport _ _ hp.1
      · exact ih _ hp.2 a ha

end TwoPointCorrelations

end OAI
