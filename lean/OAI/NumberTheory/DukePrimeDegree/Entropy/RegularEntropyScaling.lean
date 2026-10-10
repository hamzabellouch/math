import OAI.NumberTheory.DukePrimeDegree.Entropy.FourthIterateEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularEntropyTests

namespace OAI

/-! # Positive entropy at the base regular test weight -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonal_regularEntropyTest_none (d : ℕ) :
    diagonalOneParameter (regularEntropyTest d none) (regularEntropyTest_sum d none) 1 =
      diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 4 := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  rw [regularEntropyTest_none]
  congr 1
  ring

/-- The test weight indexed by `none` is the fourth iterate of the
original regular diagonal transformation. -/
theorem positive_entropy_regular_test (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1))) :
    0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d none) (regularEntropyTest_sum d none) 1)) := by
  let T := fun x => rightAction x
    (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have heq : (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d none) (regularEntropyTest_sum d none) 1)) =
      T^[4] := by
    funext x
    have hn : diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 4 =
        (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)^4 := by
      simpa only [Nat.cast_ofNat] using
        diagonalOneParameter_nat (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 4
    rw [diagonal_regularEntropyTest_none, hn]
    exact (rightAction_iterate _ 4 x).symm
  rw [heq]
  exact measureEntropy_fourth_iterate_pos μ hT hpos

end DukePrimeDegree

end

end OAI
