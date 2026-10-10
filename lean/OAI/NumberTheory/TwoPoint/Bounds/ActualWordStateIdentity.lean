import OAI.NumberTheory.TwoPoint.Walks.WeightedWordCoefficient

namespace OAI

/-! Exact evaluation of the coefficient table on the integer sites of a
word, including both endpoints of every retained departure. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def wordVertexSite {R : ℕ} (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (i : Fin (R + 1)) : ℤ :=
  n + wordDisplacement h ((List.ofFn step).take i.val)

lemma wordVertexSite_step {R : ℕ} (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (i : Fin R) :
    wordVertexSite h step n i.succ =
      wordVertexSite h step n i.castSucc + (step i).displacement h := by
  unfold wordVertexSite
  rw [wordDisplacement_take, wordDisplacement_take]
  simp only [Fin.val_succ, Fin.val_castSucc, sum_range_succ]
  have he : wordStepDisplacement h (List.ofFn step) i.val = (step i).displacement h := by
    simp [wordStepDisplacement]
  rw [he]
  ring

lemma retainedWord_eq_state_product {R m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ)
    (h : ℕ) (step : Fin R → SignedStep) (n : ℤ) :
    scalarWalkProduct h
      (retainedEdgeDeparture Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
        (fun _ => actualPaddingDegreeCut Qp L) h) n (List.ofFn step) =
      ∏ i : Fin R, paddingStateDeparture Qp Q e eligible L K (step i)
        (paddingActiveState Qp e (wordVertexSite h step n i.castSucc))
        (paddingActiveState Qp e (wordVertexSite h step n i.succ)) := by
  rw [scalarWalkProduct_ofFn]
  apply prod_congr rfl
  intro i _
  rw [retainedEdgeDeparture_eq_state Qp Q hQp hQ e]
  change paddingStateDeparture Qp Q e eligible L K (step i)
      (paddingActiveState Qp e (wordVertexSite h step n i.castSucc))
      (paddingActiveState Qp e (wordVertexSite h step n i.castSucc + (step i).displacement h)) = _
  rw [← wordVertexSite_step]

noncomputable def wordCenteredBits {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (h : ℕ) (step : Fin R → SignedStep) (n : ℤ) :
    BooleanCube (R * J) := fun k =>
  let ij := finProdFinEquiv.symm k
  decide (((w ij.2 ij.1).val : ℤ) ∣ wordVertexSite h step n ij.1.castSucc)

lemma wordCenteredBits_apply {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (i : Fin R) (j : Fin J) :
    wordCenteredBits w h step n (finProdFinEquiv (i, j)) =
      decide (((w j i).val : ℤ) ∣ wordVertexSite h step n i.castSucc) :=
  congrArg (fun ij : Fin R × Fin J =>
    decide (((w ij.2 ij.1).val : ℤ) ∣ wordVertexSite h step n ij.1.castSucc))
    ((finProdFinEquiv : Fin R × Fin J ≃ Fin (R * J)).symm_apply_apply (i, j))

lemma centeredWord_eq_state_bits {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (h : ℕ) (n : ℤ) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    scalarWalkProduct h (fun t n => centeredTuple t.tuple.primeFactors n) n (List.ofFn step) =
      centeredWordBits (fun i j => (w j i).val) (wordCenteredBits w h step n) := by
  dsimp only
  rw [scalarWalkProduct_ofFn]
  unfold centeredWordBits
  apply prod_congr rfl
  intro i _
  rw [centeredTuple_column w i hprime hdisjoint]
  apply prod_congr rfl
  intro j _
  simp only [wordCenteredBits_apply, decide_eq_true_eq]
  rfl

lemma actualWordCoefficient_integer_identity {J R m : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Qp Q : Finset ℕ) (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (h : ℕ) (n : ℤ) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    actualWordCoefficient Qp Q e eligible L K step (fun i j => (w j i).val)
      (fun i => paddingActiveState Qp e (wordVertexSite h step n i))
      (wordCenteredBits w h step n) =
    scalarWalkProduct h
      (retainedEdgeDeparture Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
        (fun _ => actualPaddingDegreeCut Qp L) h) n (List.ofFn step) *
      scalarWalkProduct h (fun t n => centeredTuple t.tuple.primeFactors n) n (List.ofFn step) := by
  dsimp only
  rw [actualWordCoefficient, retainedWord_eq_state_product Qp Q hQp hQ e,
    centeredWord_eq_state_bits w forward padding hprime hdisjoint]

end TwoPointCorrelations

end OAI
