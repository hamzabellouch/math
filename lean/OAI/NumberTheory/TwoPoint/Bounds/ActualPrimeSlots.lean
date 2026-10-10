import OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotCode
import Mathlib.Algebra.BigOperators.Associated

namespace OAI

/-! Actual prime factors give a complete bounded-slot code for a numerical word. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {R : ℕ}

abbrev ActualPrimeSlot (w : Fin R → SignedStep) :=
  Σ i : Fin R, (w i).tuple.primeFactors ⊕ (w i).padding.primeFactors

def actualSlotPrime (w : Fin R → SignedStep) (s : ActualPrimeSlot w) : ℕ :=
  match s.2 with
  | .inl p => p.val
  | .inr p => p.val

def actualSlotKind (w : Fin R → SignedStep) (s : ActualPrimeSlot w) : Bool :=
  match s.2 with
  | .inl _ => false
  | .inr _ => true

lemma actualSlotPrime_prime (w : Fin R → SignedStep) (s : ActualPrimeSlot w) :
    (actualSlotPrime w s).Prime := by
  rcases s with ⟨i, p | p⟩
  · exact Nat.prime_of_mem_primeFactors p.property
  · exact Nat.prime_of_mem_primeFactors p.property

lemma actualPrimeSlot_card_ge (w : Fin R → SignedStep)
    (hused : ∀ i, 1 ≤ (w i).tuple.primeFactors.card + (w i).padding.primeFactors.card) :
    R ≤ Fintype.card (ActualPrimeSlot w) := by
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin R))) => hused i)
  simpa only [Fintype.card_sigma, Fintype.card_sum, Fintype.card_coe,
    sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hs

theorem actualPrimeSlot_card_le (w : Fin R → SignedStep) (J M : ℕ)
    (hJ : ∀ i, (w i).tuple.primeFactors.card ≤ J)
    (hM : ∀ i, (w i).padding.primeFactors.card ≤ M) :
    Fintype.card (ActualPrimeSlot w) ≤ R * (J + M) := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ i : Fin R, ((w i).tuple.primeFactors.card + (w i).padding.primeFactors.card) := by
      simp only [Fintype.card_sum, Fintype.card_coe]
    _ ≤ ∑ _i : Fin R, (J + M) := sum_le_sum (fun i _ => Nat.add_le_add (hJ i) (hM i))
    _ = _ := by simp

noncomputable def actualPrimeSlotEquiv (w : Fin R → SignedStep) :
    ActualPrimeSlot w ≃ Fin (Fintype.card (ActualPrimeSlot w)) :=
  Fintype.equivFin (ActualPrimeSlot w)

noncomputable def actualPrimeSlotData (w : Fin R → SignedStep) :
    PrimeSlotData R (Fintype.card (ActualPrimeSlot w)) where
  forward i := (w i).forward
  row j := ((actualPrimeSlotEquiv w).symm j).1
  isPadding j := actualSlotKind w ((actualPrimeSlotEquiv w).symm j)
  prime j := actualSlotPrime w ((actualPrimeSlotEquiv w).symm j)

lemma actualSlot_factor (w : Fin R → SignedStep) (i : Fin R) (b : Bool)
    (ht : Squarefree (w i).tuple) (hq : Squarefree (w i).padding) :
    (∏ s : ActualPrimeSlot w,
      if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1) =
        if b then (w i).padding else (w i).tuple := by
  rw [Fintype.prod_sigma]
  rw [prod_eq_single i]
  · rw [Fintype.prod_sum_type]
    cases b
    · have hp := (Finset.prod_coe_sort (s := (w i).tuple.primeFactors)
        (f := fun p : ℕ => p)).trans (Nat.prod_primeFactors_of_squarefree ht)
      simpa [actualSlotKind, actualSlotPrime] using hp
    · have hp := (Finset.prod_coe_sort (s := (w i).padding.primeFactors)
        (f := fun p : ℕ => p)).trans (Nat.prod_primeFactors_of_squarefree hq)
      simpa [actualSlotKind, actualSlotPrime] using hp
  · intro j _ hji
    simp only [hji, false_and, ite_false, prod_const_one]
  · simp

lemma actualPrimeSlotData_factor (w : Fin R → SignedStep) (i : Fin R) (b : Bool)
    (ht : Squarefree (w i).tuple) (hq : Squarefree (w i).padding) :
    (actualPrimeSlotData w).factor i b = if b then (w i).padding else (w i).tuple := by
  have he := (actualPrimeSlotEquiv w).symm.prod_comp
    (fun s : ActualPrimeSlot w =>
      if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1)
  calc
    _ = ∏ s : ActualPrimeSlot w,
        if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1 := by
      unfold PrimeSlotData.factor PrimeSlotData.slots
      rw [prod_filter]
      refine Eq.trans ?_ he
      apply prod_congr rfl
      intro j _
      dsimp only [actualPrimeSlotData]
      congr 1
    _ = _ := actualSlot_factor w i b ht hq

theorem actualPrimeSlotData_word (w : Fin R → SignedStep)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding) :
    (actualPrimeSlotData w).word = List.ofFn w := by
  unfold PrimeSlotData.word
  congr 1
  funext i
  rw [actualPrimeSlotData_factor w i false (ht i) (hq i),
    actualPrimeSlotData_factor w i true (ht i) (hq i)]
  cases he : w i
  simp [actualPrimeSlotData, he]

/-- The explicit crude code and one number per observed prime class recover
both factors of every step in the original word. -/
theorem actual_word_code (w : Fin R → SignedStep)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding) :
    ∃ c : CrudeWordCode R (Fintype.card (ActualPrimeSlot w)) R,
      ∃ value : c.usedClasses → ℕ, c.numericalWord value = List.ofFn w := by
  refine ⟨(actualPrimeSlotData w).code, (fun c => (actualPrimeSlotData w).prime c.val), ?_⟩
  rw [CrudeWordCode.numericalWord_encode]
  exact actualPrimeSlotData_word w ht hq

end TwoPointCorrelations

end OAI
