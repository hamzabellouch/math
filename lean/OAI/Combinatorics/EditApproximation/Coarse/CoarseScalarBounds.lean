import OAI.Combinatorics.EditApproximation.Coarse.CoarseCellBounds
import OAI.Combinatorics.EditApproximation.Coarse.CoarseThresholdStepWork

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseDivideWithWork_den_length (a b : BinaryFraction) :
    (coarseDivideWithWork a b).1.denominator.length = Nat.size a.representation.den := by
  change (trimBitWordWithWork a.denominator).1.length = _
  exact trimBitWordWithWork_length a.denominator

 theorem coarseDivideWithWork_bounds (two a b : BinaryFraction) (V D A : ℕ)
    (hden : a.representation.den = two.representation.den)
    (hd : Nat.size two.representation.den ≤ D)
    (hgrid : (a.value / b.value).den ∣ a.representation.den)
    (hn : 0 ≤ a.value / b.value) (hv : a.value / b.value ≤ V)
    (hA : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseDivideWithWork a b).1 V D A := by
  have hd' : Nat.size a.representation.den ≤ D := by simpa only [hden] using hd
  have hval := coarseDivideWithWork_value a b hgrid
  refine ⟨(coarseDivideWithWork_den a b).trans hden,
    (coarseDivideWithWork_den_length a b).trans_le hd', ?_, ?_, ?_⟩
  · rw [hval]; exact hn
  · rw [hval]; exact hv
  · apply (coarseCompact_width _ V D (coarseCompact_divide a b) ?_ ?_).trans hA
    · rw [hval, abs_of_nonneg hn]; exact hv
    · rw [coarseDivideWithWork_den]; exact hd'

 theorem coarseChildThresholdWithWork_bounds (two allowance : BinaryFraction)
    (B q V D A : ℕ) (draw : Fin B) (hq : 0 < q)
    (ha : CoarseGridCell two allowance V D A)
    (hd : Nat.size two.representation.den ≤ D)
    (hgrid : (coarseChildThreshold B q allowance.value draw).den ∣ allowance.representation.den)
    (hA : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseChildThresholdWithWork B q allowance draw).1 V D A := by
  let num := (canonicalMulWithWork allowance (nat (draw.val + 1))).1
  let den := (canonicalMulWithWork (nat B) (nat q)).1
  have hn : num.representation.den = allowance.representation.den := by
    change (canonicalMulWithWork allowance (nat (draw.val + 1))).1.representation.den = _
    rw [canonicalMulWithWork_representation, nat_representation]
    simp only [UnreducedRational.mul, UnreducedRational.nat, mul_one]
  have hv : num.value / den.value = coarseChildThreshold B q allowance.value draw := by
    simp only [num, den, canonicalMulWithWork_value, nat_value, coarseChildThreshold]
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hu := (coarseChildThreshold_le_scale draw (q : ℚ) allowance.value hq' ha.2.2.1).trans
    ((div_le_self ha.2.2.1 (by exact_mod_cast hq)).trans ha.2.2.2.1)
  change CoarseGridCell two (coarseDivideWithWork num den).1 V D A
  exact coarseDivideWithWork_bounds two num den V D A (hn.trans ha.1) hd
    (by rw [hv, hn]; exact hgrid)
    (by rw [hv]; exact coarseChildThreshold_nonneg draw hq'.le ha.2.2.1)
    (by rw [hv]; exact hu) hA

 theorem coarseChildAllowanceWithWork_bounds (two threshold : BinaryFraction)
    (L V D A : ℕ) (hL : 0 < L) (ht : CoarseGridCell two threshold V D A)
    (hd : Nat.size two.representation.den ≤ D)
    (hgrid : (threshold.value / L).den ∣ threshold.representation.den)
    (hA : Nat.size V + 2 * D + 1 ≤ A) :
    CoarseGridCell two (coarseChildAllowanceWithWork L threshold).1 V D A := by
  change CoarseGridCell two (coarseDivideWithWork threshold (nat L)).1 V D A
  apply coarseDivideWithWork_bounds two threshold (nat L) V D A ht.1 hd
  · simpa only [nat_value] using hgrid
  · rw [nat_value]; exact div_nonneg ht.2.2.1 (by positivity)
  · rw [nat_value]
    exact (div_le_self ht.2.2.1 (by exact_mod_cast hL)).trans ht.2.2.2.1
  · exact hA

end BinaryFraction
end EditApproximation

end OAI
