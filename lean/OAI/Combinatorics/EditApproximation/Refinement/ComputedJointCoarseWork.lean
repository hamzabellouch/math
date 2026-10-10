import OAI.Combinatorics.EditApproximation.Refinement.ComputedPhysicalCoarseWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionLaw
import OAI.Combinatorics.EditApproximation.Probability.FiniteProductWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



 theorem symbolicComputedExecutionCoarseWork_expected_le (budget : ℝ)
    (hbudget : SymbolicComputedCoarseBudget (B := B) source target N depth encode budget) :
    (∫ execution, symbolicComputedExecutionCoarseWork source target N depth encode execution
      ∂physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) ≤ budget := by
  exact rejectionProductWork_expected_le _ _
    (fun outcome => symbolicComputedCoarseWork source target N depth encode outcome.2 outcome.1)
    budget hbudget

 theorem symbolicComputedExecutionCoarseWork_integrable :
    Integrable (symbolicComputedExecutionCoarseWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedCoarseWork source target N depth encode outcome.2 outcome.1
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)
end Symbolic



 theorem computedExecutionCoarseWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionCoarseWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

 theorem computedExecutionCoarseWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionCoarseWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedPhysicalCoarseWork_expected_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  exact symbolicComputedExecutionCoarseWork_expected_le source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    _ (hN source target hsize)

end EditApproximation

end OAI
