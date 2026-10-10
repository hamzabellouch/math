import OAI.NumberTheory.DukePrimeDegree.Entropy.AtomicRootEntropyZero
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularEntropyScaling
import OAI.NumberTheory.DukePrimeDegree.Geometry.CanonicalRootBasic

namespace OAI

/-! # Positive entropy gives a positive actual root coefficient -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

/-- This implication needs no numerical entropy formula. Its contrapositive
is the proved zero-entropy theorem for atomic expanding roots. -/
theorem positive_root_coefficient_of_positive_diagonal_entropy (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hpos : 0 < measureEntropy μ
      (fun x => rightAction x (diagonalOneParameter ell hell (-1)))) :
    ∃ i j : Fin (d+1), i < j ∧ 0 < canonicalRootCoefficient d μ i j := by
  by_contra! hn
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hatom (p : ↥(allPositiveRoots (d+1) \ ∅)) : ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0 := by
    have hp : p.val.1 < p.val.2 :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
    apply (canonicalRootCoefficient_zero_iff d μ hA _ _ (ne_of_lt hp)).mp
    exact le_antisymm (hn _ _ hp) (canonicalRootCoefficient_nonneg d μ _ _)
  rw [diagonal_entropy_zero_of_atomic_positive_roots d ell hell hgap μ hatom] at hpos
  exact (lt_irrefl 0 hpos)

/-- The positive-entropy hypothesis used by the prime-degree application
already supplies a positive root coefficient, without EKL Proposition3.1(3). -/
theorem positive_root_coefficient_of_regular_entropy (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1))) :
    ∃ i j : Fin (d+1), i < j ∧ 0 < canonicalRootCoefficient d μ i j := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hp := positive_entropy_regular_test d μ hA hpos
  have hn := diagonal_entropy_neg d (regularEntropyTest d none)
    (regularEntropyTest_sum d none) μ hA 1
  rw [←hn] at hp
  exact positive_root_coefficient_of_positive_diagonal_entropy d
    (regularEntropyTest d none) (regularEntropyTest_sum d none)
    (fun p => regularEntropyTest_gap d none (Finset.mem_filter.mp p.prop).2) μ hp

end DukePrimeDegree

end

end OAI
