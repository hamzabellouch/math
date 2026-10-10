import OAI.NumberTheory.Ostmann.Construction.ConstituentRangeCounts
import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalPair
import OAI.NumberTheory.Ostmann.Construction.PrimeWordEmbedding

namespace OAI

/-! # Word and prime counts for the actual final constituent pair -/
namespace Ostmann
open scoped Classical

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (e : Equiv.Perm (SurvivingConstituent role size n))
local notation "W" => primeWordEmbedding (scheduleConstituentWord role size n)
local notation "Wp" => primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))

theorem constituent_final_word_bounds
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (S A : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hA : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ A) :
    let B := 2 * 3 ^ n * Fintype.card I * S + A * S + 4
    (expandedRootTemplate role n W childBound pivotBound).WordsBounded B ∧
    (expandedRootTemplate role n Wp childBound pivotBound).WordsBounded B ∧
    (expandedRootRanges role n W ranges).WordsBounded B ∧
    (expandedRootRanges role n Wp ranges).WordsBounded B ∧
    (expandedRootRanges role n W (totalAtomUnitRanges role)).WordsBounded B ∧
    (expandedRootRanges role n Wp (totalAtomUnitRanges role)).WordsBounded B := by
  dsimp only
  have hw (i) : (W i).length ≤ S := by
    simp only [primeWordEmbedding, List.length_map, scheduleConstituentWord_length]
    exact hsize _
  have hw' (i) : (Wp i).length ≤ S := by
    simpa only [primeWordEmbedding, List.length_map] using hw i
  have ht : 2 * 3 ^ n * Fintype.card I * S + 4 ≤
      2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hr : A * S + 1 ≤ 2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hd (words : CopyScheduleAtoms role n → List (Option (SurvivingConstituent role size n)))
      (hwords : ∀ i, (words i).length ≤ S) :
      (expandedRootRanges role n words ranges).WordsBounded
        (2 * 3 ^ n * Fintype.card I * S + A * S + 4) := by
    apply WordRangeDecoration.wordsBounded_mono _ _ hr
    exact expandedScheduleRanges_words_bounded role _ ranges n A S hS hA [] _
      (fun i => by simpa only [List.length_map] using hwords i)
  exact ⟨WordTransferTemplate.wordsBounded_mono _
      (expandedRootTemplate_size role n W childBound pivotBound S hS hw) ht,
    WordTransferTemplate.wordsBounded_mono _
      (expandedRootTemplate_size role n Wp childBound pivotBound S hS hw') ht,
    hd W hw, hd Wp hw',
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n W S hS hw) ht,
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n Wp S hS hw') ht⟩

theorem constituent_final_prime_count (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    (expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
    (expandedSchedulePrimes role n n [] (fun i => (Wp i).map Sum.inl)).count ≤
      2 * ((3 ^ n * Fintype.card I * S) * (2 ^ n - 1)) := by
  have hw (i) : (W i).length ≤ S := by
    simp only [primeWordEmbedding, List.length_map, scheduleConstituentWord_length]
    exact hsize _
  have hw' (i) : (Wp i).length ≤ S := by
    simpa only [primeWordEmbedding, List.length_map] using hw i
  have hL := expandedRootPrimes_count role n S hS W hw
  have hR := expandedRootPrimes_count role n S hS Wp hw'
  omega

theorem constituent_final_top_count (S : ℕ) (hsize : ∀ i, size i ≤ S) :
    (constituentPrimePairChecks (SurvivingConstituent role size n) ++
      atomPairChecks W ++ atomPairChecks Wp).length ≤
        3 * (3 ^ n * Fintype.card I * S) ^ 2 := by
  have hw (i) : (W i).length ≤ S := by
    simp only [primeWordEmbedding, List.length_map, scheduleConstituentWord_length]
    exact hsize _
  have hw' (i) : (Wp i).length ≤ S := by
    simpa only [primeWordEmbedding, List.length_map] using hw i
  have hcard : Fintype.card (Σ i, Fin (size i)) ≤ Fintype.card I * S := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (f := size) (g := fun _ => S)
        (fun i _ => hsize i))
  have hK : Fintype.card (SurvivingConstituent role size n) ≤
      3 ^ n * Fintype.card I * S := by
    have hh := copyScheduleAtoms_card_le (fun i : Σ a, Fin (size a) => role i.1) n
    exact hh.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left (3 ^ n) hcard)
  have hchecks := atomPairChecks_length (fun i : SurvivingConstituent role size n => [some i])
    1 (by intro i; rfl)
  simp only [Nat.mul_one] at hchecks
  have hL := atomPairChecks_length W S hw
  have hR := atomPairChecks_length Wp S hw'
  have ha := Nat.pow_le_pow_left hK 2
  have hb := Nat.pow_le_pow_left
    (Nat.mul_le_mul_right S (copyScheduleAtoms_card_le role n)) 2
  simp only [List.length_append, constituentPrimePairChecks]
  omega

end
end Ostmann

end OAI
