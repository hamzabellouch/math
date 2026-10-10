import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorStoredMasks
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTaskSpace

namespace OAI

/-! # All-outcome storage of sampled families and incidence lists -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace SeparatorStoredMasks

variable {g : ℕ}

/-- Eight arrays of incidence lists, their headers, and the four sampled
families with each local mask represented by its indexed bits. -/
def storage (families : Fin 4 → Array (Finset (Fin g))) : ℕ :=
  ∑ i : Fin 4, (
    ((containsStore (families i)).toList.map Array.size).sum +
      ((avoidsStore (families i)).toList.map Array.size).sum +
      2 * 2 ^ g + (g + 1) * (families i).size)

theorem storage_le (families : Fin 4 → Array (Finset (Fin g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    storage families ≤ (44 * (g + 1) + 96) * 2 ^ (2 * g) := by
  have hp : ∀ i : Fin 4,
      ((containsStore (families i)).toList.map Array.size).sum +
        ((avoidsStore (families i)).toList.map Array.size).sum +
        2 * 2 ^ g + (g + 1) * (families i).size ≤
          (11 * (g + 1) + 24) * 2 ^ (2 * g) := by
    intro i
    have hc := SeparatorIncidenceTable.preprocess_storage g (families i)
      (fun j S => decide (decode j ⊆ S))
    have ha := SeparatorIncidenceTable.preprocess_storage g (families i)
      (fun j S => decide (Disjoint (decode j) S))
    change ((containsStore (families i)).toList.map Array.size).sum ≤
      2 ^ g * (families i).size at hc
    change ((avoidsStore (families i)).toList.map Array.size).sum ≤
      2 ^ g * (families i).size at ha
    have hi := hsize i
    have hpow : 2 ^ g ≤ 2 ^ (2 * g) := Nat.pow_le_pow_right (by decide) (by omega)
    have hmul := Nat.mul_le_mul_left (2 ^ g) hi
    have hm : 2 ^ g * (11 * 2 ^ g) = 11 * 2 ^ (2 * g) := by
      rw [two_mul g, pow_add]
      ring
    rw [hm] at hmul
    have hf := Nat.mul_le_mul_left (g + 1) hi
    have ht := Nat.mul_le_mul_left (11 * (g + 1)) hpow
    nlinarith only [hc, ha, hmul, hf, ht, hpow]
  unfold storage
  calc
    _ ≤ ∑ _ : Fin 4, (11 * (g + 1) + 24) * 2 ^ (2 * g) := Finset.sum_le_sum (fun i _ => hp i)
    _ = _ := by simp; ring

end SeparatorStoredMasks

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem separator_table_rate_le_capacity :
    2 ^ (2 * (2 * blockHalf n 0)) ≤ compressionDictionaryCapacity n := by
  unfold compressionDictionaryCapacity
  apply Nat.pow_le_pow_right (by decide)
  simp only [blockHalf, Matrix.cons_val_zero]
  omega

theorem sampled_separator_storage (h : R.PrimeHistory) (hn : 2200 ≤ n)
    (draws : R.SeparatorDraws h hn) :
    SeparatorStoredMasks.storage (SeparatorCheck.sampledFamilies draws) ≤
      inputScale R.input ^ 2 * compressionDictionaryCapacity n := by
  let g := 2 * blockHalf n 0
  let u := inputScale R.input
  let C := compressionDictionaryCapacity n
  have hs : ∀ i, (SeparatorCheck.sampledFamilies draws i).size ≤ 11 * 2 ^ g := by
    intro i
    simpa only [SeparatorCheck.sampledFamilies, Array.size_ofFn,
      SeparatorExpectation.RoundedParameters.counts, SeparatorCheck.theta, g] using
      (separatorParameters h.1.1.2 hn).counts_le i
  have ht := SeparatorStoredMasks.storage_le (SeparatorCheck.sampledFamilies draws) hs
  have hg : g + 1 ≤ u := by unfold g u inputScale blockHalf; simp only [Matrix.cons_val_zero]; omega
  have hu : 2200 ≤ u := by unfold u inputScale; omega
  have hcoef : 44 * (g + 1) + 96 ≤ u ^ 2 := by nlinarith only [hg, hu]
  exact ht.trans (Nat.mul_le_mul hcoef (separator_table_rate_le_capacity (n := n)))

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
