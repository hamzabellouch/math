import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedDyads

namespace OAI

/-! Exact fixed-angular low-height stopping rows, retaining the original
coefficients, product support, and inverse-binomial factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def angular_distinguishedScaleStoppedRow (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
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
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

def angular_distinguishedScaleStopped (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h early k else 0

def angular_scaleFirstStoppedSum (ℓ : ℤ) (m : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (h : ℕ) (early : Bool) : ℂ :=
  ∑ i ∈ Finset.range m, angular_distinguishedScaleStopped ℓ i ρ ξ Ct H X h early

def angular_distinguishedStoppedDyad (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
        (if a*b ∈ centralProductEnvelope X then
          centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

theorem angular_distinguishedScaleStoppedRow_dyads (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h early d =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h early d q j k := by
  unfold angular_distinguishedScaleStoppedRow
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact stopped_matrix_dyadic _ _
    (fun a ha => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) ha)
    (fun b hb => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) hb)
    _ _ _ X

end CubicFirstMoment

end

end OAI
