import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixCheckList
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorEncodedBounds

namespace OAI

/-! # Expected scans when one family is reused for the full check list -/

noncomputable section

namespace LowSpaceSubsetSum.TopCoordinates

open RepresentationMoments SeparatorExpectation

variable {n g : ℕ} (C : TopCoordinates n g)

abbrev CheckInputs (n : ℕ) := Array (Entry (Fin n)) × Array (Entry (Fin n))

def checkInputSize (checks : List (CheckInputs n)) : ℕ :=
  (checks.map (fun p => p.1.size + p.2.size)).sum

def totalScans (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (checks : List (CheckInputs n)) : ℕ :=
  (checks.map (fun p => (C.check families target p.1.toList p.2.toList).scans)).sum

theorem mean_totalScans (S : RoundedParameters g) (u : ℕ)
    (hu : 256 ≤ u) (hnu : n ≤ u) (hgu : g + 1 ≤ u)
    (target : ℤ) (checks : List (CheckInputs n))
    (hleft : ∀ p ∈ checks, ∀ x ∈ p.1.toList, ∀ i,
      (SeparatorCheck.localMask i (C.encodeEntry x).mask).card = S.c i)
    (hright : ∀ p ∈ checks, ∀ x ∈ p.2.toList, ∀ i,
      (SeparatorCheck.localMask i (C.encodeEntry x).mask).card = g / 2 - S.c i) :
    mean (fun draws : IndependentFamilies g S.e S.counts =>
      (C.totalScans (familyArrays draws) target checks : ℝ)) ≤
      (checkInputSize checks : ℝ) * (u : ℝ) ^ 22 *
        (2 : ℝ) ^ (((4 * g : ℕ) : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  induction checks with
  | nil => simp [totalScans, checkInputSize, mean]
  | cons p checks ih =>
    have hp := C.mean_scans_polynomial S u hu hnu hgu target p.1.toList p.2.toList
      (hleft p (by simp)) (hright p (by simp))
    simp only [Array.length_toList, Nat.cast_add] at hp
    have ht := ih (fun q hq => hleft q (by simp [hq])) (fun q hq => hright q (by simp [hq]))
    simp only [totalScans, List.map_cons, List.sum_cons, Nat.cast_add] at ht ⊢
    rw [mean_add]
    simp only [checkInputSize, List.map_cons, List.sum_cons, Nat.cast_add] at ht ⊢
    nlinarith

/-- The check list is fixed before the separator draws, so no independence
between the individual checks is used in this tail bound. -/
theorem totalScans_tail (S : RoundedParameters g) (u : ℕ)
    (hu : 256 ≤ u) (hnu : n ≤ u) (hgu : g + 1 ≤ u)
    (target : ℤ) (checks : List (CheckInputs n))
    (hleft : ∀ p ∈ checks, ∀ x ∈ p.1.toList, ∀ i,
      (SeparatorCheck.localMask i (C.encodeEntry x).mask).card = S.c i)
    (hright : ∀ p ∈ checks, ∀ x ∈ p.2.toList, ∀ i,
      (SeparatorCheck.localMask i (C.encodeEntry x).mask).card = g / 2 - S.c i)
    (T : ℝ) (hT : 0 < T) :
    finiteUniformProbability (fun draws : IndependentFamilies g S.e S.counts =>
      T < (C.totalScans (familyArrays draws) target checks : ℝ)) ≤
      ((checkInputSize checks : ℝ) * (u : ℝ) ^ 22 *
        (2 : ℝ) ^ (((4 * g : ℕ) : ℝ) * (1 - binaryEntropy (1 / 4)))) / T := by
  classical
  let (i : Fin 4) : Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i)) :=
    (Finset.powersetCard_nonempty.mpr (by simpa using S.size_le i)).to_subtype
  have hmarkov := finite_count_markov
    (fun draws : IndependentFamilies g S.e S.counts =>
      C.totalScans (familyArrays draws) target checks) hT
  rw [finiteUniformProbability_eq_cardRatio]
  simp only [Fintype.card_subtype] at ⊢
  apply hmarkov.trans
  exact div_le_div_of_nonneg_right
    (C.mean_totalScans S u hu hnu hgu target checks hleft hright) hT.le

end LowSpaceSubsetSum.TopCoordinates

end

end OAI
