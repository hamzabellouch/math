import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordCircuit
import OAI.NumberTheory.TwoPoint.Bounds.ActualWordStateIdentity

namespace OAI

/-! A finite list of every literal in a weighted word: the padding
state at each endpoint, its centered-prime tests, and every occurrence
in the prohibited-site DNFs. Equal primes share one residue coordinate. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

abbrev ActualWordInput {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) :=
  (Fin (R + 1) × Fin m) ⊕
    ((Fin R × Fin J) ⊕ (Fin (R + 1) × Fin (Fintype.card (ProhibitedInputs data.pairs h s))))

noncomputable def actualWordInputEquiv {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) : ActualWordInput data s R m ≃ Fin (Fintype.card (ActualWordInput data s R m)) :=
  Fintype.equivFin _

noncomputable def actualWordLiterals {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) :
    Fin (Fintype.card (ActualWordInput data s R m)) → ↥(data.P ∪ data.Q) × ℤ := fun i =>
  match (actualWordInputEquiv data s R m).symm i with
  | .inl (r, j) => (⟨(e j).val, mem_union_right _ (e j).property⟩, wordVertexSite h step 0 r)
  | .inr (.inl (r, j)) => (label (r, j), wordVertexSite h step 0 r.castSucc)
  | .inr (.inr (r, j)) =>
      ((data.prohibitedLiteral s j).1, wordVertexSite h step 0 r + (data.prohibitedLiteral s j).2)

noncomputable def actualWordQIndex {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) (r : Fin (R + 1)) (j : Fin m) :
    Fin (Fintype.card (ActualWordInput data s R m)) :=
  actualWordInputEquiv data s R m (.inl (r, j))

noncomputable def actualWordPIndex {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) (k : Fin (R * J)) : Fin (Fintype.card (ActualWordInput data s R m)) :=
  actualWordInputEquiv data s R m (.inr (.inl (finProdFinEquiv.symm k)))

noncomputable def actualWordBadIndex {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) (r : Fin (R + 1)) (j : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    Fin (Fintype.card (ActualWordInput data s R m)) :=
  actualWordInputEquiv data s R m (.inr (.inr (r, j)))

noncomputable def actualWordIntegerBits {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) (n : ℤ) :
    BooleanCube (Fintype.card (ActualWordInput data s R m)) :=
  residueCircuitInputs (primeResidueModuli (data.P ∪ data.Q))
    (primeLiteralCoordinate (data.P ∪ data.Q) (actualWordLiterals data s e step label))
    (primeLiteralTest (data.P ∪ data.Q) (actualWordLiterals data s e step label))
    (fun j => (n : ZMod (primeResidueModuli (data.P ∪ data.Q) j)))

lemma actualWordQIndex_eval {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) (n : ℤ) (r : Fin (R + 1)) (j : Fin m) :
    actualWordIntegerBits data s e step label n (actualWordQIndex data s R m r j) =
      decide (((e j).val : ℤ) ∣ wordVertexSite h step n r) := by
  rw [actualWordIntegerBits, primeLiteral_integer_input]
  simp only [actualWordLiterals, actualWordQIndex, Equiv.symm_apply_apply, wordVertexSite,
    zero_add]
  rfl

lemma actualWordBadIndex_eval {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) (n : ℤ) (r : Fin (R + 1))
    (j : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    actualWordIntegerBits data s e step label n (actualWordBadIndex data s R m r j) =
      prohibitedInputAt data.pairs h s (wordVertexSite h step n r) j := by
  rw [actualWordIntegerBits, primeLiteral_integer_input]
  simp only [actualWordLiterals, actualWordBadIndex, Equiv.symm_apply_apply,
    ProhibitedPrimeFamily.prohibitedLiteral, prohibitedInputAt, wordVertexSite, zero_add,
    add_assoc]

lemma actualWordPIndex_eval {h J M R m : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (e : Fin m ≃ data.Q)
    (w : ColumnPrimeAssignment J R P) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val) (n : ℤ) (k : Fin (R * J)) :
    actualWordIntegerBits data s e step label n (actualWordPIndex data s R m k) =
      wordCenteredBits w h step n k := by
  rw [actualWordIntegerBits, primeLiteral_integer_input]
  simp only [actualWordLiterals, actualWordPIndex, Equiv.symm_apply_apply]
  simp only [hlabel, wordCenteredBits, wordVertexSite, zero_add]
  rfl

end TwoPointCorrelations

end OAI
