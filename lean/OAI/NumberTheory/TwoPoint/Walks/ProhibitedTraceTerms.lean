import OAI.NumberTheory.TwoPoint.Bounds.GoodDesignatedWordSum
import OAI.NumberTheory.TwoPoint.Bounds.WeightedDivisorWord

namespace OAI

/-! Literal centered and designated terms of the prohibited-vertex trace expansion. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def prohibitedCenteredAverage {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) : ℝ :=
  (data.residueLaw B hB).average (fun x => weight x * (∏ t,
    ((if ((label t).val : ℤ) ∣ (x (label t)).val + wordDisplacement h (word.take t.1.val)
      then (1 : ℝ) else 0) - ((label t).val : ℝ)⁻¹)) *
        attachedCatalogAvoidance data s B D word x)

noncomputable def prohibitedDesignatedTerm {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) (U : Finset (Fin R × Fin J)) : ℝ :=
  if LitConsistent (nonsingletonSlots label \ U) label (tupleForcedTarget data hB word label) then
    designatedReciprocal (fun p : ↥(data.P ∪ data.Q) => p.val)
      (singletonLabels label) (nonsingletonSlots label \ U) U label *
        (data.residueLaw B hB).average
          (fun x => weight x * |prohibitedWordDifference data hB s D word label base U x|)
  else 0

lemma prohibitedDesignatedTerm_nonneg {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) (hw : ∀ x, 0 ≤ weight x)
    (U : Finset (Fin R × Fin J)) :
    0 ≤ prohibitedDesignatedTerm data hB s D word label base weight U := by
  unfold prohibitedDesignatedTerm
  split_ifs
  · apply mul_nonneg
    · unfold designatedReciprocal
      positivity
    · exact (data.residueLaw B hB).average_nonneg (fun x => mul_nonneg (hw x) (abs_nonneg _))
  · exact le_rfl

theorem prohibited_centering_bound {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) (hw : ∀ x, 0 ≤ weight x)
    (hdep : ∀ x y, (∀ i, i ∉ univ.image label → x i = y i) → weight x = weight y) :
    |prohibitedCenteredAverage data hB s D word label weight| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        prohibitedDesignatedTerm data hB s D word label base weight U := by
  have hb := uniform_weighted_centered_word_majorant B
    (fun p : ↥(data.P ∪ data.Q) => p.val) (fun p => (data.prime p).pos)
    (fun p => hB _ p.property) label (tupleForcedTarget data hB word label) base
    (fun t => forcedResidue_lt B (label t).val (data.prime _).pos
      (hB _ (label t).property) (wordDisplacement h (word.take t.1.val)))
    weight (attachedCatalogAvoidance data s B D word) hw hdep
  unfold prohibitedCenteredAverage
  change |(FiniteLaw.independent _).average _| ≤ _
  rw [uniform_weighted_divisor_word_average B
    (fun p : ↥(data.P ∪ data.Q) => p.val) (fun p => (data.prime p).pos)
    (fun p => hB _ p.property) label
    (fun t => wordDisplacement h (word.take t.1.val)) weight
    (attachedCatalogAvoidance data s B D word)]
  apply hb.trans_eq
  apply sum_congr rfl
  intro U _
  unfold prohibitedDesignatedTerm prohibitedWordDifference
  simp only [designation_sdiff_decidable (fun a b => Classical.propDecidable (a = b))
    (inferInstance : DecidableEq (Fin R × Fin J))]
  rfl

end TwoPointCorrelations

end OAI
