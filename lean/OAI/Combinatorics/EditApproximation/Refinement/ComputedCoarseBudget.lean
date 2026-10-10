import OAI.Combinatorics.EditApproximation.Refinement.ComputedPhysicalWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyMemoCoarse
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Polynomial coarse-sampling budgets for the computed dimensions. -/

namespace EditApproximation
open MeasureTheory Filter

section Coarse
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



 def SymbolicComputedCoarseBudget (budget : ℝ) : Prop :=
  ∀ draw, integral (coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi))
      (symbolicComputedCoarseWork (B := B) source target N depth encode draw) ≤ budget

 theorem symbolicComputedCoarseWork_expected_le
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hM : M = (integerParameters N).M) (hJ : J = intervalTreeDepth M source.length)
    (hB : B = (integerParameters N).B)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
    (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ (16384 * inputHeight N + 5))
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8) :
    SymbolicComputedCoarseBudget (B := B) source target N depth encode
      (computedWidthEnvelope N * computedCoarseWidthOverhead N) := by
  intro draw
  have hH : 105 ≤ inputHeight N := (by omega : 105 ≤ inputSmallLog N).trans
    (computed_smallLog_le_height N)
  apply physicalFamilyMemoCoarseWork_expected_le source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
    (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    draw B depth (computedParameterP_pos N) hN hell hB hsize hdepth hinverse
    (16384 * inputHeight N + 5) encode hinjective hbounded _ (by rfl) (computedWidthEnvelope N)
  intro coarse
  let initial := clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse)
  let root := localFinalRootRequest (M := M) (J := J) target N (integerParameters N).T
    (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length)
  let tree := physicalFamilyDependencyTree source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
    (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    initial (computedParameterP_pos N) draw root
  have hv := physicalFamilyDependencyTree_valid source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
    (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    initial (computedParameterP_pos N) draw hN hell hM rfl rfl rfl le_rfl
    (fun pass => (scheduledSeedFactor_bounds N pass).1)
    (fun pass => (scheduledSeedFactor_bounds N pass).2) root
  have hd : tree.depth = intervalTreeDepth (integerParameters N).M source.length := by
    rw [physicalFamilyDependencyTree_depth]
    exact hJ.trans (congrArg (fun m => intervalTreeDepth m source.length) hM)
  have hk := physicalFamilyDependencyTree_rank source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
    (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    initial (computedParameterP_pos N) draw rfl rfl rfl root
  have hw := computed_widthWork_le_envelope N source.length hN (by omega) hell hH tree
    (by simpa only [hM] using hv) hd hk
  simpa only [hM] using hw

 theorem symbolicComputedCoarseBudget_mono (a b : ℝ) (hab : a ≤ b)
    (h : SymbolicComputedCoarseBudget (B := B) source target N depth encode a) :
    SymbolicComputedCoarseBudget (B := B) source target N depth encode b := fun draw => (h draw).trans hab

end Coarse
end EditApproximation

end OAI
