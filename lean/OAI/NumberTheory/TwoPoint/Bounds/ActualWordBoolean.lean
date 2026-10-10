import OAI.NumberTheory.TwoPoint.Bounds.ActualWordInputs
import OAI.NumberTheory.TwoPoint.Walks.ClosedWordStateMask
import OAI.NumberTheory.TwoPoint.Walks.WordDegreeSupport

namespace OAI

/-! The actual closed scalar word is precisely the bounded-state Boolean
function to which weighted finite-interval comparison applies. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def actualWordBoolean {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (Q : Finset ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (p : Fin R → Fin J → ℕ) (eligible : ℕ → ℕ → Prop) (L K : ℝ)
    (x : BooleanCube (Fintype.card (ActualWordInput data s R m))) : ℝ :=
  let S := fun r => activeState (fun i => x (actualWordQIndex data s R m r i))
  if (∀ r, (S r).card ≤ ⌊400 * Real.log L⌋₊) ∧
      (prohibitedWordKeepCircuit data.pairs h s (actualWordBadIndex data s R m)).eval x = true
    then actualWordCoefficient data.Q Q e (fun t => eligible t.tuple) L K step p S
      (fun k => x (actualWordPIndex data s R m k))
    else 0

lemma actualWordBoolean_integer {h J M R m : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (Q : Finset ℕ)
    (hQ : Q ⊆ retainedPrimeDivisors data.Q) (e : Fin m ≃ data.Q)
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (eligible : ℕ → ℕ → Prop) (L K : ℝ) (hL : 1 ≤ L) (n : ℤ)
    (hR : 0 < R) (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    actualWordBoolean data s Q e step (fun i j => (w j i).val) eligible L K
      (actualWordIntegerBits data s e step label n) =
    scalarWalkProduct h
      (maskedSignedIntegerWeight Q actualPaddingCoefficient eligible (actualPaddingVertex data.Q)
        (fun d => centeredTuple d.primeFactors) L K (fun _ => actualPaddingDegreeCut data.Q L)
        h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z))
      n (List.ofFn step) := by
  dsimp only
  let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
  let x := actualWordIntegerBits data s e step label n
  have hS (r : Fin (R + 1)) :
      activeState (fun i => x (actualWordQIndex data s R m r i)) =
        paddingActiveState data.Q e (wordVertexSite h step n r) := by
    unfold paddingActiveState
    congr 1
    funext i
    exact actualWordQIndex_eval data s e step label n r i
  have hbits : (fun k => x (actualWordPIndex data s R m k)) = wordCenteredBits w h step n :=
    funext (actualWordPIndex_eval data s e w step label hlabel n)
  have hmask : (prohibitedWordKeepCircuit data.pairs h s
      (actualWordBadIndex data s R m)).eval x = true ↔
      ∀ r, ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (wordVertexSite h step n r) :=
    prohibitedWordKeepCircuit_eval data.pairs h s data.whole_squarefree _ _ x
      (actualWordBadIndex_eval data s e step label n)
  rw [closed_actual_word_state w forward padding hprime hdisjoint data.Q Q
    data.primeQ hQ e eligible L K h n hR hclosed]
  change actualWordBoolean data s Q e step (fun i j => (w j i).val) eligible L K x = _
  simp only [actualWordBoolean, hS, hbits, hmask]
  let S := fun r => paddingActiveState data.Q e (wordVertexSite h step n r)
  let coeff := actualWordCoefficient data.Q Q e (fun t => eligible t.tuple) L K step
    (fun i j => (w j i).val) S (wordCenteredBits w h step n)
  have ht : (if ∀ r, (S r).card ≤ ⌊400 * Real.log L⌋₊ then coeff else 0) = coeff :=
    actualWordCoefficient_truncation data.Q Q e (fun t => eligible t.tuple) L K step
      (fun i j => (w j i).val) S _ hR hL
  dsimp only [S, coeff, step] at ht ⊢
  by_cases hm : ∀ r, ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
      (wordVertexSite h (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)) n r)
  · simpa [hm] using ht
  · simp [hm]

end TwoPointCorrelations

end OAI
