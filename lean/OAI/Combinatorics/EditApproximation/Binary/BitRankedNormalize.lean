import OAI.Combinatorics.EditApproximation.Binary.BitQueryNormalize
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The denominator condition is used only at the semantic values of
smaller requests.  Strong induction then establishes the actual binary
program's value and normalized trace without assuming its own output. -/

namespace EditApproximation

section Normalize
variable {κ : Type*} (rank : κ → ℕ)
  (raw : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
  (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
  (semantic : κ → ℚ)
  (hrefines : ∀ key, BitQuery.Refines (fun word value => word.value = value) (raw key) (expected key))
  (hbody : ∀ key, (expected key).value (fun child => semantic child.val) = semantic key)
  (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : κ → ℕ)
  (hden : ∀ key, (semantic key).den ∣ bitWordValue base ^ remaining key)



include hrefines hbody hden in
theorem rankedNormalizeBody_correct (key : κ) :
    (rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) key).value =
        semantic key ∧
    BitQuery.RefinesOn
      (fun child => rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val)
      (fun word value => word.value = value)
      (rankedNormalizeBody rank raw base hbase remaining key) (expected key) := by
  have hall : ∀ level key, rank key = level →
      (rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) key).value =
        semantic key ∧
      BitQuery.RefinesOn
        (fun child => rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val)
        (fun word value => word.value = value)
        (rankedNormalizeBody rank raw base hbase remaining key) (expected key) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel
      let oracle := fun child : {child : κ // rank child < rank key} =>
        rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val
      have horacle : (fun child => (oracle child).value) = (fun child => semantic child.val) := by
        funext child
        exact (ih (rank child.val) (hlevel ▸ child.property) child.val rfl).1
      have hraw : ((raw key).value oracle).value = semantic key := by
        have hv := ((hrefines key).value_keys oracle).1
        rw [horacle, hbody key] at hv
        exact hv
      have hd : ((raw key).value oracle).value.den ∣ bitWordValue base ^ remaining key := by
        rw [hraw]
        exact hden key
      have hn := ((hrefines key).onOracle oracle).normalize base hbase (remaining key) hd
      refine ⟨?_, hn⟩
      rw [rankedBitProgramValue]
      exact hn.value_keys.1.trans (by rw [horacle]; exact hbody key)
  exact hall (rank key) key rfl


include hrefines hbody hden in
theorem rankedNormalizeBody_width (key : κ) (B V : ℕ)
    (hB : base.length ≤ B) (hV : |semantic key| ≤ (V : ℚ)) :
    (rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) key).width ≤
      Nat.size V + 2 * (remaining key * B + 1) + 1 := by
  let oracle := fun child : {child : κ // rank child < rank key} =>
    rankedBitProgramValue rank (rankedNormalizeBody rank raw base hbase remaining) child.val
  have horacle : (fun child => (oracle child).value) = (fun child => semantic child.val) := by
    funext child
    exact (rankedNormalizeBody_correct rank raw expected semantic hrefines hbody base hbase remaining
      hden child.val).1
  have hraw : ((raw key).value oracle).value = semantic key := by
    have hv := ((hrefines key).value_keys oracle).1
    rw [horacle, hbody key] at hv
    exact hv
  have hd : ((raw key).value oracle).value.den ∣ bitWordValue base ^ remaining key := by
    rw [hraw]
    exact hden key
  have hv : |((raw key).value oracle).value| ≤ (V : ℚ) := by rw [hraw]; exact hV
  rw [rankedBitProgramValue]
  change ((BitQuery.normalize (raw key) base hbase (remaining key)).value oracle).width ≤ _
  rw [(BitQuery.normalize_value (raw key) base hbase (remaining key) oracle hd).1]
  exact BinaryFraction.powerDenominatorWithWork_width ((raw key).value oracle) base hbase
    (remaining key) V B hB hd hv

end Normalize
end EditApproximation

end OAI
