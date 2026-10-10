import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughRows
import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusionLog

namespace OAI

/-! The actual early-stopped row has a logarithmic reciprocal-prime
exclusion bound. Zero coefficients are kept explicit rather than requiring
roughness of an artificial ambient support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_prime_factors_card_log {a : Eisenstein} (ha : primary a) :
    ((primaryPrimeFactors a).card:ℝ) ≤ Real.log (norm a)/Real.log 2 := by
  have hh := primary_prime_divisor_card_log (primaryPrimeFactors a)
    (fun p hp => (primaryPrimeFactor_spec ha hp).1) a (primary_ne_zero ha)
  have he : (primaryPrimeFactors a).filter (fun p => p ∣ a) = primaryPrimeFactors a :=
    Finset.filter_eq_self.mpr (fun p hp => (primaryPrimeFactor_spec ha hp).2)
  rwa [he] at hh

lemma rough_pair_prime_reciprocal_log {a b : Eisenstein} (ha : primary a) (hb : primary b)
    {X R : ℝ} (hR : 0 < R) (haX : norm a ≤ X) (hbX : norm b ≤ X)
    (har : ∀ p ∈ primaryPrimeFactors a, R ≤ norm p)
    (hbr : ∀ p ∈ primaryPrimeFactors b, R ≤ norm p) :
    (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) ≤
      (2*Real.log X/Real.log 2)/R := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hca : ((primaryPrimeFactors a).card:ℝ) ≤ Real.log X/Real.log 2 :=
    (primary_prime_factors_card_log ha).trans (div_le_div_of_nonneg_right
      (Real.log_le_log (norm_pos_of_ne_zero (primary_ne_zero ha)) haX) hlog2.le)
  have hcb : ((primaryPrimeFactors b).card:ℝ) ≤ Real.log X/Real.log 2 :=
    (primary_prime_factors_card_log hb).trans (div_le_div_of_nonneg_right
      (Real.log_le_log (norm_pos_of_ne_zero (primary_ne_zero hb)) hbX) hlog2.le)
  have hc : ((primaryPrimeFactors a ∪ primaryPrimeFactors b).card:ℝ) ≤
      2*Real.log X/Real.log 2 := by
    have hh : ((primaryPrimeFactors a ∪ primaryPrimeFactors b).card:ℝ) ≤
        (primaryPrimeFactors a).card+(primaryPrimeFactors b).card := by
      exact_mod_cast Finset.card_union_le (primaryPrimeFactors a) (primaryPrimeFactors b)
    calc
      _ ≤ ((primaryPrimeFactors a).card:ℝ)+((primaryPrimeFactors b).card:ℝ) := hh
      _ ≤ Real.log X/Real.log 2+Real.log X/Real.log 2 := add_le_add hca hcb
      _ = _ := by ring
  calc
    _ ≤ ∑ _p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/R := by
      apply Finset.sum_le_sum
      intro p hp
      apply one_div_le_one_div_of_le hR
      rcases Finset.mem_union.mp hp with hp | hp
      · exact har p hp
      · exact hbr p hp
    _ = ((primaryPrimeFactors a ∪ primaryPrimeFactors b).card:ℝ)/R := by
      simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right hc hR.le

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stopped_pair_prime_reciprocal_log {X ξ δ l b : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδone : δ ≤ 1) (hbX : b ≤ X)
    (W : ι → ℝ → ℂ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (hj : j ≤ h)
    (e : Eisenstein) {a c : Eisenstein}
    (ha : a ∈ stoppedIntervalSupport ι X l b e)
    (hc : c ∈ stoppedIntervalSupport ι X l b e)
    (ha0 : stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early) a ≠ 0)
    (hc0 : stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early) c ≠ 0)
    (hR : 0 < min (X^ξ) (geometricBinLower (1+δ) X h)) :
    (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors c, 1/norm p) ≤
      (2*Real.log X/Real.log 2)/min (X^ξ) (geometricBinLower (1+δ) X h) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have ha' := stoppedIntervalSupport_spec X l b e ha
  have hc' := stoppedIntervalSupport_spec X l b e hc
  apply rough_pair_prime_reciprocal_log ha'.1 hc'.1 hR
    (ha'.2.2.trans hbX) (hc'.2.2.trans hbX)
  · intro p hp
    exact stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) 0
      (1+δ) Z Q W (Real.rpow_pos_of_pos hXp _)
      (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
      j k h early hj ha0 (primaryPrimeFactor_spec ha'.1 hp).1
      (primaryPrimeFactor_spec ha'.1 hp).2
  · intro p hp
    exact stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) 0
      (1+δ) Z Q W (Real.rpow_pos_of_pos hXp _)
      (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
      j k h early hj hc0 (primaryPrimeFactor_spec hc'.1 hp).1
      (primaryPrimeFactor_spec hc'.1 hp).2

end CubicFirstMoment

end

end OAI
