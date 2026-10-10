import OAI.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeResidueProductCutoff_loss {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (res : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i)
    (hmM : ∀ j i, m j i ≤ M j) (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / L j) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (r : J → ℝ≥0) (hr : ∀ j, 0 < r j) :
    (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j)
      (hL j) (m j) (res j) (hm j) (hmM j) (hsize j))).mean
      (fun z => 1 - scalarCubeProductCutoff I (fun j => (r j : ℝ))
        (fun j i => (z j i : ℝ) / L j)) ≤
      ∑ j, scalarCubeResidueCutoffBudget I A (r j) (L j) (M j) := by
  let q : ∀ j, FiniteProbabilityWeights (IntegerScalarCubeBox I (L j)) :=
    fun j => scalarCubeResidueWeights I (L j) (M j)
      (hL j) (m j) (res j) (hm j) (hmM j) (hsize j)
  let b : ∀ j, IntegerScalarCubeBox I (L j) → ℝ := fun j z =>
    inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r j : ℝ))
      scalarCubeFace (fun i => (z i : ℝ) / L j)
  have hloss := FiniteProbabilityWeights.pi_cutoff_loss q b
    (fun _ _ => inequalityBoundaryCutoff_range _ _ _)
  change (FiniteProbabilityWeights.pi q).mean (fun z => 1 - ∏ j, b j (z j)) ≤ _
  apply hloss.trans
  exact Finset.sum_le_sum (fun j _ => scalarCubeResidueCutoff_loss I (L j) (M j)
    (hL j) (m j) (res j) (hm j) (hmM j) (hsize j) (hsmall j) A hA (hr j))

theorem scalarCubeResidueProductCutoff_bias {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (res : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i)
    (hmM : ∀ j i, m j i ≤ M j) (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / L j) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (r : J → ℝ≥0) (hr : ∀ j, 0 < r j)
    (F : (∀ j, IntegerScalarCubeBox I (L j)) → ℂ) (hF : ∀ z, ‖F z‖ ≤ 1)
    {ζ : ℝ} (hbias : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j =>
      scalarCubeResidueWeights I (L j) (M j) (hL j) (m j) (res j)
        (hm j) (hmM j) (hsize j))).complexMean F‖) :
    ζ - (∑ j, scalarCubeResidueCutoffBudget I A (r j) (L j) (M j)) ≤
      ‖(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j)
        (hL j) (m j) (res j) (hm j) (hmM j) (hsize j))).complexMean
        (fun z => (scalarCubeProductCutoff I (fun j => (r j : ℝ))
          (fun j i => (z j i : ℝ) / L j) : ℂ) * F z)‖ :=
  FiniteProbabilityWeights.cutoff_bias_lower _ _ F
    (fun _ => scalarCubeProductCutoff_range _ _) hF hbias
    (scalarCubeResidueProductCutoff_loss L M hL m res hm hmM hsize hsmall A hA r hr)

end Erdos3

end

end OAI
