import OAI.Combinatorics.EditApproximation.Queries.QueryGroupInputs
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSetupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandGuardWork

namespace OAI

namespace EditApproximation.BinaryFraction

def queryGroupLabelsBitBudget (M B R : ℕ) : ℕ :=
  groupSampleCountBitBudget B + 8 * (groupSampleCountWordBudget B) +
    M * (R + 4) + 4

theorem queryGroupLabelsWithWork_bounds (M Q b B R : ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hh : h.width ≤ B)
    (hR : ∀ i, (draw i).2 ≤ R) :
    (queryGroupLabelsWithWork M Q b h draw).1.length ≤ M ∧
    (queryGroupLabelsWithWork M Q b h draw).2 ≤ queryGroupLabelsBitBudget M B R := by
  let count := groupSampleCountWithWork M Q b h
  let test := naturalEqualWithWork (bitWordValue count.1) M
  have hc := groupSampleCountWithWork_bounds M Q b h B hM hQ hb hh
  have hsize : Nat.size (bitWordValue count.1) ≤ groupSampleCountWordBudget B :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans hc.1
  have ht := naturalEqualWithWork_cost (bitWordValue count.1) M (groupSampleCountWordBudget B)
    hsize (by unfold groupSampleCountWordBudget; omega)
  by_cases he : (naturalEqualWithWork (bitWordValue (groupSampleCountWithWork M Q b h).1) M).1 = true
  · simp only [queryGroupLabelsWithWork, he, ↓reduceIte, List.length_finRange]
    refine ⟨le_rfl, ?_⟩
    change count.2 + test.2 + M + 2 ≤ _
    have hcc : count.2 ≤ groupSampleCountBitBudget B := hc.2
    change test.2 ≤ _ at ht
    unfold queryGroupLabelsBitBudget
    nlinarith only [hcc, ht, Nat.zero_le R, Nat.zero_le M]
  · have hlabels := arithmeticMapWithWork_cost draw (List.finRange (groupSampleCount M Q b h.value)) R
      (fun i _ => hR i)
    have hlen : groupSampleCount M Q b h.value ≤ M := Nat.min_le_left _ _
    simp only [List.length_finRange] at hlabels
    have hlabels' := hlabels.trans (Nat.mul_le_mul_right _ hlen)
    simp only [queryGroupLabelsWithWork, he, Bool.false_eq_true, ↓reduceIte]
    let indices := queryFinRange (bitWordValue count.1) (groupSampleCount M Q b h.value)
      (groupSampleCountWithWork_value M Q b h)
    change (arithmeticMapWithWork draw indices).1.length ≤ M ∧
      count.2 + test.2 + (arithmeticMapWithWork draw indices).2 + indices.length + 2 ≤ _
    have hindices : indices = List.finRange (groupSampleCount M Q b h.value) :=
      queryFinRange_value _ _ _
    rw [hindices]
    simp only [arithmeticMapWithWork_value, List.length_map, List.length_finRange]
    refine ⟨hlen, ?_⟩
    have hcc : count.2 ≤ groupSampleCountBitBudget B := hc.2
    change test.2 ≤ _ at ht
    unfold queryGroupLabelsBitBudget
    have heq : M * (R + 4) = M * (R + 3) + M := by ring
    rw [heq]
    omega

end EditApproximation.BinaryFraction

end OAI
