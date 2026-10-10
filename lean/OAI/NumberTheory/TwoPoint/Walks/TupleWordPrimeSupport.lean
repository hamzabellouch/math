import OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
import OAI.NumberTheory.TwoPoint.Walks.TupleOccurrences
import OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueEvent

namespace OAI

/-! Match the tuple/padding reciprocal factors to the full numerical word support. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def tuplePrimeSupport {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : Finset ℕ :=
  univ.biUnion (fun j => (univ.image (w j)).image Subtype.val)

lemma mem_tuplePrimeSupport {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (p : ℕ) :
    p ∈ tuplePrimeSupport w ↔ ∃ j i, (w j i).val = p := by
  simp only [tuplePrimeSupport, mem_biUnion, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨j, q, ⟨i, rfl⟩, rfl⟩
    exact ⟨j, i, rfl⟩
  · rintro ⟨j, i, rfl⟩
    exact ⟨j, w j i, ⟨i, rfl⟩, rfl⟩

lemma tuplePrimeSupport_reciprocal {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∏ p ∈ tuplePrimeSupport w, (p : ℝ)⁻¹) = columnReciprocalWeight w := by
  unfold tuplePrimeSupport columnReciprocalWeight
  rw [prod_biUnion]
  · apply prod_congr rfl
    intro j _
    rw [prod_image]
    exact fun _ _ _ _ h => Subtype.ext h
  · intro j _ l _ hjl
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨a, _, rfl⟩ := mem_image.mp hp
    obtain ⟨b, _, hab⟩ := mem_image.mp hq
    exact disjoint_left.mp (hdisjoint j l (Ne.symm hjl)) a.property (hab ▸ b.property)

lemma tupleWord_primeSupport {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (q : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (hq : ∀ i, q i ≠ 0) :
    wordDivisorPrimeSupport (columnTupleWord w forward q) =
      tuplePrimeSupport w ∪ paddingPrimeSupport q := by
  ext p
  have ht (i : Fin R) : columnTuple w i ≠ 0 :=
    (columnTuple_squarefree w i hprime hdisjoint).ne_zero
  simp only [wordDivisorPrimeSupport, columnTupleWord, mem_biUnion, List.mem_toFinset,
    List.mem_ofFn, mem_union, mem_tuplePrimeSupport, paddingPrimeSupport, mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, hp⟩
    rw [Nat.primeFactors_mul (hq i) (ht i), mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inr ⟨i, hp⟩
    · rw [columnTuple_primeFactors w i hprime hdisjoint] at hp
      obtain ⟨j, _, hj⟩ := mem_image.mp hp
      exact Or.inl ⟨j, i, hj⟩
  · rintro (⟨j, i, rfl⟩ | ⟨i, hp⟩)
    · refine ⟨⟨forward i, columnTuple w i, q i⟩, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      apply Or.inr
      rw [columnTuple_primeFactors w i hprime hdisjoint]
      exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
    · refine ⟨⟨forward i, columnTuple w i, q i⟩, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inl hp

lemma tupleWord_reciprocal {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (q : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (hq : ∀ i, q i ≠ 0)
    (hsep : Disjoint (tuplePrimeSupport w) (paddingPrimeSupport q)) :
    columnReciprocalWeight w * (∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹) =
      ∏ p ∈ wordDivisorPrimeSupport (columnTupleWord w forward q), (p : ℝ)⁻¹ := by
  rw [tupleWord_primeSupport w forward q hprime hdisjoint hq, prod_union hsep,
    tuplePrimeSupport_reciprocal w hdisjoint]

/-- Fixed signs and the numerical step list recover every tuple column
and every padding. Thus the full-word counting bound applies injectively
to the actual matrix-word catalog. -/
theorem columnTupleWord_injective {J R : ℕ} {P : Fin J → Finset ℕ}
    (forward : Fin R → Bool) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun a : ColumnPrimeAssignment J R P × (Fin R → ℕ) =>
      columnTupleWord a.1 forward a.2) := by
  intro a b hab
  have hsteps := List.ofFn_injective hab
  apply Prod.ext
  · funext j i
    have htuple := congrArg SignedStep.tuple (congrFun hsteps i)
    have hvalues := primeTuple_injective hprime hdisjoint htuple
    exact congrFun hvalues j
  · funext i
    exact congrArg SignedStep.padding (congrFun hsteps i)

end TwoPointCorrelations

end OAI
