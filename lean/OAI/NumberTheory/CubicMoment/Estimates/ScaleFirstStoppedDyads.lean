import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStopping
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMatrixDyads

namespace OAI

/-! The exact dyadic form of each original stopped row. The inverse
binomial scalar and both stopping predicates are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedStoppedAlpha (ρ ξ X : ℝ) (q : ℕ × ℕ × ℕ) : Eisenstein → ℂ :=
  stoppedAlpha (centralPrimaryFactors X) (centralPrimaryFactors X)
    primeDetectorCutoff (X^ξ)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.2)

def distinguishedStoppedBeta (i : ℕ) (ρ ξ X : ℝ) (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) : Eisenstein → ℂ :=
  stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1 h
      (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early)

def distinguishedStoppedSide (X : ℝ) : Finset Eisenstein :=
  stoppedFactorSupport (primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X)) X

def distinguishedStoppedDyad (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
        (if a*b ∈ centralProductEnvelope X then
          centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

theorem distinguishedScaleStoppedRow_dyads (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    distinguishedScaleStoppedRow i ρ ξ Ct H X h early d =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k := by
  unfold distinguishedScaleStoppedRow
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
