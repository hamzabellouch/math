import OAI.NumberTheory.Ostmann.Construction.ConstituentPairFactors
import OAI.NumberTheory.Ostmann.Construction.ExpandedPrimeCount
import OAI.NumberTheory.Ostmann.Arithmetic.TotalAtomUnits

namespace OAI

/-! # Concrete word and support counts for the actual two histories -/

namespace Ostmann
open scoped Classical

theorem WordTransferTemplate.wordsBounded_mono {V : Type*} {n B C : ℕ}
    (T : WordTransferTemplate V n) (hT : T.WordsBounded B) (hBC : B ≤ C) : T.WordsBounded C := by
  induction T with
  | leaf w => exact hT.trans hBC
  | node d L R ihL ihR => exact ⟨hT.1.trans hBC, ihL hT.2.1, ihR hT.2.2⟩

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))

/-- One linear word budget covers both exact templates, all inherited units,
and every supplied range involving at most `A` current atoms. -/
theorem constituent_pair_word_bounds
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (S A : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hA : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ A) :
    let B := 2 * 3 ^ n * Fintype.card I * S + A * S + 4
    (expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound).WordsBounded B ∧
    (expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound).WordsBounded B ∧
    (expandedRootRanges role n (insertedConstituentWord role size n) ranges).WordsBounded B ∧
    (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges).WordsBounded B ∧
    (expandedRootRanges role n (insertedConstituentWord role size n) (totalAtomUnitRanges role)).WordsBounded B ∧
    (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) (totalAtomUnitRanges role)).WordsBounded B := by
  dsimp only
  have hw := insertedConstituentWord_length_le role size n S hS hsize
  have hwR (i) : (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i).length ≤ S := by simpa only [List.length_map] using hw i
  have ht : 2 * 3 ^ n * Fintype.card I * S + 4 ≤
      2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hr : A * S + 1 ≤ 2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hd (words : CopyScheduleAtoms role n → List (Option ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))))
      (hwords : ∀ i, (words i).length ≤ S) :
      (expandedRootRanges role n words ranges).WordsBounded
        (2 * 3 ^ n * Fintype.card I * S + A * S + 4) := by
    apply WordRangeDecoration.wordsBounded_mono _ _ hr
    exact expandedScheduleRanges_words_bounded role _ ranges n A S hS hA [] _
      (fun i => by simpa only [List.length_map] using hwords i)
  exact ⟨WordTransferTemplate.wordsBounded_mono _ (expandedRootTemplate_size role n (insertedConstituentWord role size n) childBound pivotBound S hS hw) ht,
    WordTransferTemplate.wordsBounded_mono _ (expandedRootTemplate_size role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound S hS hwR) ht,
    hd (insertedConstituentWord role size n) hw, hd ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) hwR,
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n (insertedConstituentWord role size n) S hS hw) ht,
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) S hS hwR) ht⟩

theorem constituent_pair_prime_count (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    (expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl ((insertedConstituentWord role size n) i))).count +
    (expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i))).count ≤
      2 * ((3 ^ n * Fintype.card I * S) * (2 ^ n - 1)) := by
  have hw := insertedConstituentWord_length_le role size n S hS hsize
  have hwR (i) : (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i).length ≤ S := by simpa only [List.length_map] using hw i
  have hL := expandedRootPrimes_count role n S hS (insertedConstituentWord role size n) hw
  have hR := expandedRootPrimes_count role n S hS ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) hwR
  exact (Nat.add_le_add hL hR).trans_eq (by omega)

theorem constituent_pair_top_count (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) ++ atomPairChecks (insertedConstituentWord role size n) ++ atomPairChecks ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))).length ≤
      (Fintype.card ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) ^ 2 + 2 * (3 ^ n * Fintype.card I * S) ^ 2 := by
  have hw := insertedConstituentWord_length_le role size n S hS hsize
  have hwR (i) : (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i).length ≤ S := by simpa only [List.length_map] using hw i
  have he := atomPairChecks_length (fun i : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) => [some i]) 1 (by intro i; rfl)
  simp only [Nat.mul_one] at he
  have hL := atomPairChecks_length (insertedConstituentWord role size n) S hw
  have hR := atomPairChecks_length ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) S hwR
  have hc := Nat.mul_le_mul_right S (copyScheduleAtoms_card_le role n)
  have hs := Nat.pow_le_pow_left hc 2
  simp only [List.length_append, constituentPrimePairChecks]
  omega

end
end Ostmann

end OAI
