import OAI.NumberTheory.TwoPoint.Bounds.WeightedDesignationBound
import OAI.NumberTheory.TwoPoint.Walks.TupleWordPrimeSupport

namespace OAI

/-! The actual designated tuple-word majorant has precisely the weight used by column rank. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem weighted_designation_le_tuple_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (q : Fin R → ℕ)
    (hprime : ∀ j, ∀ r ∈ P j, r.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hq : ∀ i, q i ≠ 0) (hsep : Disjoint (tuplePrimeSupport w) (paddingPrimeSupport q))
    (B h : ℕ) (p : ι → ℕ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : Fin R × Fin J → ι) (target : Fin R × Fin J → Fin B) (base : ι → Fin B)
    (U : Finset (Fin R × Fin J)) (hU : U ⊆ nonsingletonSlots label) (H C : ℝ)
    (hH : 1 ≤ H) (hC : 0 ≤ C) (hpH : ∀ i ∈ nonsingletonLabels label, H ≤ p i)
    (hS : ∀ i ∈ univ.image label, p i ∈ wordDivisorPrimeSupport (columnTupleWord w forward q))
    (hcover : ∀ r ∈ wordDivisorPrimeSupport (columnTupleWord w forward q), ∃ i, p i = r)
    (weight G : (ι → Fin B) → ℝ) (hw : ∀ x, 0 ≤ weight x) (hwC : ∀ x, weight x ≤ C)
    (hG : ∀ x, |G x| ≤ 1)
    (hretain : ∀ x, weight x ≠ 0 →
      RetainedMainTests p (univ.image label) h B (columnTupleWord w forward q) x) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => weight x * |selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|) ≤
      (C * 2 ^ (singletonLabels label).card) * columnReciprocalWeight w *
        ∏ r ∈ paddingPrimeSupport q, (r : ℝ)⁻¹ := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hb := weighted_designation_bound B h p hinj hp hpB (columnTupleWord w forward q)
    label target base U hU H C hHp hC hpH hS hcover weight G hw hwC hG hretain
  have he : H⁻¹ ^ (∑ i ∈ nonsingletonLabels label,
      extraReciprocalExponent (litOccurrences label (designationLit U) i).card
        (unlitOccurrences label (designationLit U) i).card) ≤ 1 :=
    pow_le_one₀ (by positivity) ((inv_le_one₀ hHp).mpr hH)
  rw [designation_sdiff_decidable (fun a b => Classical.propDecidable (a = b))
    (inferInstance : DecidableEq (Fin R × Fin J)) _ _] at hb
  apply hb.trans
  calc
    _ ≤ (C * 2 ^ (singletonLabels label).card) * 1 *
        ∏ r ∈ wordDivisorPrimeSupport (columnTupleWord w forward q), (r : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
    _ = _ := by
      rw [mul_one, ← tupleWord_reciprocal w forward q hprime hdisjoint hq hsep]
      ring

end TwoPointCorrelations

end OAI
