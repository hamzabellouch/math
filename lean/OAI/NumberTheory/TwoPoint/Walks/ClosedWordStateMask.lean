import OAI.NumberTheory.TwoPoint.Bounds.ActualWordStateIdentity
import OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths

namespace OAI

/-! The actual closed masked word is its finite-state coefficient times
one indicator for survival of all its vertices. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma wordVertexSite_closed {R : ℕ} (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0) :
    wordVertexSite h step n (Fin.last R) = wordVertexSite h step n 0 := by
  simp [wordVertexSite, List.take_of_length_le (by simp : (List.ofFn step).length ≤ R), hclosed]

lemma closed_word_vertex_iff {R : ℕ} (hR : 0 < R) (h : ℕ)
    (step : Fin R → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0) (keep : ℤ → Prop) :
    (∀ i : Fin R, keep (wordVertexSite h step n i.castSucc)) ↔
      ∀ i : Fin (R + 1), keep (wordVertexSite h step n i) := by
  constructor
  · intro hi i
    by_cases hb : i.val < R
    · have he : (⟨i.val, hb⟩ : Fin R).castSucc = i := Fin.ext rfl
      simpa only [he] using hi ⟨i.val, hb⟩
    · have he : i = Fin.last R := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [he, wordVertexSite_closed h step n hclosed]
      exact hi ⟨0, hR⟩
  · intro hi i
    exact hi i.castSucc

lemma closed_word_mask {R : ℕ} (hR : 0 < R) (h : ℕ)
    (step : Fin R → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0) (keep : ℤ → Prop) :
    scalarWalkProduct h (fun _ z => vertexIndicator keep z) n (List.ofFn step) =
      if ∀ i : Fin (R + 1), keep (wordVertexSite h step n i) then 1 else 0 := by
  rw [scalarWalkProduct_ofFn]
  change (∏ i : Fin R, vertexIndicator keep (wordVertexSite h step n i.castSucc)) = _
  by_cases hv : ∀ i : Fin R, keep (wordVertexSite h step n i.castSucc)
  · have hv' := (closed_word_vertex_iff hR h step n hclosed keep).mp hv
    simp [vertexIndicator, hv, hv']
  · have hv' : ¬∀ i : Fin (R + 1), keep (wordVertexSite h step n i) :=
      fun hh => hv ((closed_word_vertex_iff hR h step n hclosed keep).mpr hh)
    rw [ite_eq_right hv']
    obtain ⟨i, hi⟩ := not_forall.mp hv
    exact prod_eq_zero (mem_univ i) (by simp [vertexIndicator, hi])

lemma closed_actual_word_state {J R m : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Qp Q : Finset ℕ) (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : ℕ → ℕ → Prop) (L K : ℝ) (h : ℕ) (n : ℤ)
    (hR : 0 < R) (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (keep : ℤ → Prop) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    scalarWalkProduct h
      (maskedSignedIntegerWeight Q actualPaddingCoefficient eligible (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L K (fun _ => actualPaddingDegreeCut Qp L) h keep)
      n (List.ofFn step) =
      if ∀ i : Fin (R + 1), keep (wordVertexSite h step n i) then
        actualWordCoefficient Qp Q e (fun t => eligible t.tuple) L K step (fun i j => (w j i).val)
          (fun i => paddingActiveState Qp e (wordVertexSite h step n i)) (wordCenteredBits w h step n)
      else 0 := by
  dsimp only
  rw [show maskedSignedIntegerWeight Q actualPaddingCoefficient eligible (actualPaddingVertex Qp)
      (fun d => centeredTuple d.primeFactors) L K (fun _ => actualPaddingDegreeCut Qp L) h keep =
      fun t z => vertexIndicator keep z *
        signedIntegerWeight Q actualPaddingCoefficient (eligible t.tuple) (actualPaddingVertex Qp)
          (centeredTuple t.tuple.primeFactors) L K (actualPaddingDegreeCut Qp L) h t z *
        vertexIndicator keep (z + t.displacement h) from rfl]
  rw [closed_masked_scalar_word hR h _ n hclosed _ _
    (fun z => by unfold vertexIndicator; split_ifs <;> simp)]
  rw [closed_signed_word_factorization Q actualPaddingCoefficient (fun t => eligible t.tuple)
    (actualPaddingVertex Qp) (fun t => centeredTuple t.tuple.primeFactors) L K
    (fun _ => actualPaddingDegreeCut Qp L) h n
    (List.ofFn (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)))
    (actualPaddingVertex_ne_zero Qp)
    (fun t q _ z => centeredTuple_padding_periodic t.tuple.primeFactors h t.tuple
      (fun p hp => (Nat.mem_primeFactors.mp hp).2.1) q z) hclosed]
  rw [← actualWordCoefficient_integer_identity w forward padding hprime hdisjoint Qp Q hQp hQ e]
  rw [closed_word_mask hR h _ n hclosed keep]
  split_ifs <;> simp

end TwoPointCorrelations

end OAI
