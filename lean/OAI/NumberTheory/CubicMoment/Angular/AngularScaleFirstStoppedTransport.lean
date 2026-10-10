import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedGeometry
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTransport

namespace OAI

/-! Exact fixed-angular low-height stopping rows, retaining the original
coefficients, product support, and inverse-binomial factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_distinguishedStoppedDyad_to_row (ℓ : ℤ) (i : ℕ) {ρ ξ X : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (Ct : ℕ) (H : ℝ)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) (hk : 1 ≤ q.2.1)
    (hZ : 2 ≤ (if early then X^(9/25:ℝ) else X^(38/100:ℝ)))
    (hBX : stoppedNormDyadLength k ≤ X)
    (hj : geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ q.1)
    (hh : geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h) :
    angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k =
      ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
        ∑ b ∈ stoppedIntervalSupport (Fin i) X (stoppedNormDyadLength k/2)
          (stoppedNormDyadLength k) 1,
          distinguishedStoppedAlpha ρ ξ X q a*
            stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
              (distinguishedShiftedSideTest ρ X h early q) b*
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  unfold angular_distinguishedStoppedDyad
  apply Finset.sum_congr rfl
  intro a ha
  have hap := (distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1).1
  calc
    _ = distinguishedStoppedAlpha ρ ξ X q a *
        ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
          distinguishedStoppedBeta i ρ ξ X h early d q b*
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [←mul_assoc]
      congr 1
      exact centeredHeightKernel_envelope ℓ primeProductEnvelope hXp
        (primeProductWeights.upper_support ()) H ((1+Real.log X)^Ct) X
        (primary_mul hap (distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1).1)
    _ = distinguishedStoppedAlpha ρ ξ X q a *
        ∑ b ∈ stoppedIntervalSupport (Fin i) X (stoppedNormDyadLength k/2)
          (stoppedNormDyadLength k) 1,
          stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
            (distinguishedShiftedSideTest ρ X h early q) b*
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
      congr 1
      simpa only [distinguishedStoppedBeta_as_weights,distinguishedStoppedSide,
        stoppedFactorSupport,centralPrimaryFactors,distinguishedShiftedSideTest] using
        stoppedBeta_shifted_sharp_dyad_to_row hρ hρ₂ hX hXF
          (Real.rpow_pos_of_pos hXp ξ) hZ (distinguishedStoppingWeights d) (X^(2/5:ℝ))
          q.1 q.2.1 h k hk early
          (fun b => centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b))
          hBX hj hh
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end CubicFirstMoment

end

end OAI
