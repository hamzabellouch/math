import OAI.NumberTheory.CubicMoment.Estimates.RestrictedNoStopParameters
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

def stoppingFailedPrefix (ρ F Q : ℝ) (h : ℕ) (r m : Eisenstein) : Prop :=
  norm r*primeSurrogate
    (primeBinPrefix (primaryPrimeFactors m) (geometricPrimeBin ρ F) h)
    (geometricPrimeBin ρ F) (geometricBinLower ρ F) < Q

def distinguishedScaleStoppedRow (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  let F := Real.exp primeProductWeights.radius*X
  let I := if early then (stoppingLabelBox ρ F).filter (fun q => q.1 < h)
    else stoppingLabelBox ρ F
  ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
    ∑ a ∈ primaryPairSupport (primaryElementBall F) (primaryElementBall F),
      ∑ b ∈ primaryPairSupport (centralPrimaryFactors X) (primaryElementBall F),
        stoppedAlpha (primaryElementBall F) (primaryElementBall F) primeDetectorCutoff (X^ξ)
            (stoppingRemainingTest (geometricPrimeBin ρ F) q.1 q.2.2) a *
          stoppedBeta (centralPrimaryFactors X) (primaryElementBall F)
            (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ)
            (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
              q.1 q.2.1 h (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early) b *
          (if a*b ∈ centralProductEnvelope X then
            centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

def distinguishedScaleStopped (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      distinguishedScaleStoppedRow i ρ ξ Ct H X h early k else 0

theorem distinguishedScaleRow_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (Ct : ℕ) (H : ℝ) (h : ℕ)
        (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleLength k < X^(69/200:ℝ) →
      distinguishedScaleRow i 0 ξ Ct H X k =
        restrictedNoStopCenteredValue (centralPrimaryFactors X)
          (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ) ρ
          (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) 0 primeProductEnvelope
          H ((1+Real.log X)^Ct) X X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        distinguishedScaleStoppedRow i ρ ξ Ct H X h true k +
        distinguishedScaleStoppedRow i ρ ξ Ct H X h false k := by
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
    (centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X)
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

theorem distinguishedLowScaleRows_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (Ct : ℕ) (H : ℝ) (h : ℕ),
      distinguishedLowScaleRows i 0 ξ Ct H X =
        distinguishedScaleNoStop i ρ ξ Ct H X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        distinguishedScaleStopped i ρ ξ Ct H X h true +
        distinguishedScaleStopped i ρ ξ Ct H X h false := by
  filter_upwards [distinguishedScaleRow_two_stage i ξ] with X hX
  intro ρ hρ hρ₂ Ct H h
  unfold distinguishedLowScaleRows distinguishedScaleNoStop distinguishedScaleStopped
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
