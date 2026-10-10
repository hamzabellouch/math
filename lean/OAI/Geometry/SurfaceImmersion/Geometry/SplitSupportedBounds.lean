import OAI.Geometry.SurfaceImmersion.Geometry.SplitSupportedTarget
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds

namespace OAI

/-!
Finite-order bounds for the actual partition split.  A fixed partition has
bounded derivatives of every fixed order.  Consequently the split costs a
constant depending only on that partition and the order, uniformly over all
short scales at most one and linearly in the target seminorm.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

open SmallModes (Base)
open JetPolynomial (SupportedField supportedWeightedSeminorm
  weightedBound_of_supportedSeminorm supportedSeminorm_le_of_weightedBound)
open WeightedEstimates

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}

/-- A partition coefficient bundled on its actual compact support. -/
def supportedWeight (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    SupportedField (F := ℝ) (P.supportCompact i) :=
  ContDiffMapSupportedIn.of_support_subset (P.smooth i) subset_closure

@[simp] theorem supportedWeight_apply (P : CompactPhasePartition ι (K : Set Base) U)
    (i : ι) (x : Base) : P.supportedWeight i x = P.weight i x := rfl

/-- Unit-scale derivatives of the fixed partition coefficient. -/
def weightSize (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) (i : ι) : ℝ :=
  supportedWeightedSeminorm (P.supportCompact i) 1 m (P.supportedWeight i)

theorem weightSize_nonneg (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) (i : ι) :
    0 ≤ P.weightSize m i := apply_nonneg _ _

theorem weight_weightedBound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : (s : ℝ) ≤ 1) :
    WeightedBound univ s m (P.weightSize m i) (P.weight i) := by
  exact (weightedBound_of_supportedSeminorm (1 : ℝ≥0) m
    (P.supportedWeight i)).shrink_scale s.coe_nonneg hs

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The product estimate with the coefficient's explicit derivative size. -/
theorem splitSupported_bound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (A : SupportedField (F := F) K) :
    supportedWeightedSeminorm (P.pieceSupport i) s m (P.splitSupported A i) ≤
      (2 ^ m * P.weightSize m i) * supportedWeightedSeminorm K s m A := by
  have hA := weightedBound_of_supportedSeminorm s m A
  have hprod := (P.weight_weightedBound m i s hs1).smul_real uniqueDiffOn_univ
    s.coe_nonneg (P.weightSize_nonneg m i) (apply_nonneg _ _)
    (P.smooth i).contDiffOn A.contDiff.contDiffOn hA
  exact supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (mul_nonneg (by positivity) (P.weightSize_nonneg m i))
      (apply_nonneg _ _)) (P.splitSupported A i) hprod

/-- A single constant works for every member of the finite partition. -/
def splitConstant (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) : ℝ :=
  1 + ∑ i, 2 ^ m * P.weightSize m i

theorem one_le_splitConstant (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) :
    1 ≤ P.splitConstant m := by
  have hsum : 0 ≤ ∑ i, 2 ^ m * P.weightSize m i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (P.weightSize_nonneg m i))
  change 1 ≤ 1 + ∑ i, 2 ^ m * P.weightSize m i
  linarith

theorem coefficient_le_splitConstant (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) : 2 ^ m * P.weightSize m i ≤ P.splitConstant m := by
  classical
  have hi : 2 ^ m * P.weightSize m i ≤ ∑ j, 2 ^ m * P.weightSize m j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (by positivity) (P.weightSize_nonneg m j))
      (Finset.mem_univ i)
  change 2 ^ m * P.weightSize m i ≤ 1 + ∑ j, 2 ^ m * P.weightSize m j
  linarith

/-- The fixed finite partition costs no negative power of the scale. -/
theorem splitSupported_uniform_bound (P : CompactPhasePartition ι (K : Set Base) U)
    (m : ℕ) (i : ι) (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) ≤ 1)
    (A : SupportedField (F := F) K) :
    supportedWeightedSeminorm (P.pieceSupport i) s m (P.splitSupported A i) ≤
      P.splitConstant m * supportedWeightedSeminorm K s m A :=
  (P.splitSupported_bound m i s hs hs1 A).trans
    (mul_le_mul_of_nonneg_right (P.coefficient_le_splitConstant m i) (apply_nonneg _ _))

end ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

end

end OAI
