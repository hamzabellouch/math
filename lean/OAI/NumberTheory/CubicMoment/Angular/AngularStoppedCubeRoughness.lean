import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeRoughness
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_stopped_pair_prime_reciprocal_log (ℓ : ℤ) {X ξ δ l b : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδone : δ ≤ 1) (hbX : b ≤ X)
    (W : ι → ℝ → ℂ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (hj : j ≤ h)
    (e : Eisenstein) {a c : Eisenstein}
    (ha : a ∈ stoppedIntervalSupport ι X l b e)
    (hc : c ∈ stoppedIntervalSupport ι X l b e)
    (ha0 : angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early) a ≠ 0)
    (hc0 : angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
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
    exact angularStoppedRowCoefficient_early_roughness ℓ X (X^ξ) (X^(2/5:ℝ)) 0
      (1+δ) Z Q W (Real.rpow_pos_of_pos hXp _)
      (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
      j k h early hj ha0 (primaryPrimeFactor_spec ha'.1 hp).1
      (primaryPrimeFactor_spec ha'.1 hp).2
  · intro p hp
    exact angularStoppedRowCoefficient_early_roughness ℓ X (X^ξ) (X^(2/5:ℝ)) 0
      (1+δ) Z Q W (Real.rpow_pos_of_pos hXp _)
      (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
      j k h early hj hc0 (primaryPrimeFactor_spec hc'.1 hp).1
      (primaryPrimeFactor_spec hc'.1 hp).2

end CubicFirstMoment

end

end OAI
