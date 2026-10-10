import OAI.NumberTheory.CubicMoment.Angular.AngularRestrictedNoStopParameters
import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedDyads
import OAI.NumberTheory.CubicMoment.Estimates.RoughProductTwoStage
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedScaleRows

namespace OAI

/-! The actual low scale-first rows satisfy the two-stage stopping
identity. The no-stop prefix test and both independent stopped matrices
are retained exactly. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_distinguishedScaleRow_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (Ct : ℕ) (H : ℝ) (h : ℕ)
        (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleLength k < X^(69/200:ℝ) →
      distinguishedScaleRow i ℓ ξ Ct H X k =
        restrictedNoStopCenteredValue (centralPrimaryFactors X)
          (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ) ρ
          (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) ℓ primeProductEnvelope
          H ((1+Real.log X)^Ct) X X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h true k +
        angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h false k := by
  filter_upwards [eventually_distinguishedScale_low_initial i ξ,
    eventually_ge_atTop (1:ℝ)] with X hstart hX
  intro ρ hρ hρ₂ Ct H h k hk
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have he := roughProduct_matrix_two_stage (centralProductEnvelope X) (centralPrimaryFactors X)
    hρ hρ₂ hF (fun _ hn => centralProductEnvelope_spec hn)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (distinguishedScaleCoefficient i ξ X k) (fun r _ hr => hstart k hk r hr)
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (9/25:ℝ) ≤ 38/100))
    h primeDetectorCutoff (X^ξ)
    (centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X)
  unfold distinguishedScaleRow
  rw [he]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · unfold restrictedNoStopCenteredValue stoppingFailedPrefix
      simp only [centralProductEnvelope]
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hp : norm r*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors d)
            (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) h)
          (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) < X^(9/25:ℝ)
      <;> by_cases hq : norm r*primeSurrogate (primaryPrimeFactors d)
          (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) < X^(38/100:ℝ)
      all_goals simp only [hp,hq,and_self,and_true,and_false,ite_true,ite_false]
    · rfl
  · rfl

theorem angular_distinguishedLowScaleRows_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (Ct : ℕ) (H : ℝ) (h : ℕ),
      distinguishedLowScaleRows i ℓ ξ Ct H X =
        angular_distinguishedScaleNoStop ℓ i ρ ξ Ct H X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        angular_distinguishedScaleStopped ℓ i ρ ξ Ct H X h true +
        angular_distinguishedScaleStopped ℓ i ρ ξ Ct H X h false := by
  filter_upwards [angular_distinguishedScaleRow_two_stage ℓ i ξ] with X hX
  intro ρ hρ hρ₂ Ct H h
  unfold distinguishedLowScaleRows angular_distinguishedScaleNoStop angular_distinguishedScaleStopped
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : distinguishedScaleLength k < X^(69/200:ℝ)
  · simp only [hk,ite_true]
    exact hX ρ hρ hρ₂ Ct H h k hk
  · simp only [hk,ite_false,zero_add]

end CubicFirstMoment

end

end OAI
