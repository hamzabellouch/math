import OAI.Combinatorics.ProgressionColoring.ConstructionArithmetic

namespace OAI

/-!
# Denominators after the construction's dilation

The actual dilation contains every primary part of a period of size at most
twice the cutoff whose prime is at most the square of the dimension. Thus a
reduced denominator is either one or exceeds the square of the dimension.
-/

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- The actual dilation kills every period up to the dimension squared. -/
theorem short_period_dvd_lambda {k h : ℕ} (hh : 0 < h)
    (hmax : h ≤ 2 * cutoff k) (hshort : h ≤ dimension k ^ 2) :
    h ∣ lambda k :=
  short_period_dvd_dilation hh hshort hmax

/-- A nonintegral dilated fraction has denominator larger than the dimension
squared. This applies to every natural numerator, including zero. -/
theorem reducedDenominator_gt_of_not_dvd {k h t : ℕ} (hh : 0 < h)
    (hmax : h ≤ 2 * cutoff k) (hnot : ¬ h ∣ lambda k * t) :
    dimension k ^ 2 < h / Nat.gcd h (lambda k * t) := by
  have hparts : ∀ p : ℕ, p.Prime → p ≤ dimension k ^ 2 →
      p ^ h.factorization p ∣ lambda k := by
    intro p hp hp0
    exact primary_part_dvd_dilation hp hp0 hh hmax
  rcases reducedDenominator_eq_one_or_gt_of_primary_parts (t := t) hh hparts with
    hone | hlarge
  · have he : h = Nat.gcd h (lambda k * t) := by
      calc
        h = (h / Nat.gcd h (lambda k * t)) * Nat.gcd h (lambda k * t) :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left h (lambda k * t))).symm
        _ = Nat.gcd h (lambda k * t) := by rw [hone, one_mul]
    exact (hnot (he.symm ▸ Nat.gcd_dvd_right h (lambda k * t))).elim
  · exact hlarge

end QuantitativeVanDerWaerden.ConstructionModel

end OAI
