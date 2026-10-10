import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.BranchWeights

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryMaskLaws

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open AllFieldHistoryMasks AllFieldHistoryBranchWeights AllFieldParameters
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def parentCenter (allocation : Allocation) (side : Fin 3) (h : Active K tick)
    (a b : Statistic h) : ℝ :=
  ∑ u : JointPopulation.Shape,
    (activeCounts allocation 1 h u : ℝ) /
      population allocation 1 (h.val.1.source, h.val.2) *
        (leftLaw h u side a * rightLaw h u side b)

theorem center_eq_parentCenter (allocation : Allocation) (side : Fin 3)
    (i : MaskIndex K tick) :
    center allocation side i = parentCenter allocation side i.1 (i.2.1 i.1) (i.2.2 i.1) := by
  have hw (c : testedClasses allocation i) :
      classWeight (fun c : testedClasses allocation i => Positions allocation 1 c.val) c =
        (activeCounts allocation 1 c.val.1 c.val.2 : ℝ) /
          population allocation 1 (i.1.val.1.source, i.1.val.2) := by
    rw [selected_classWeight_formula allocation (by decide : 0 < (1 : ℕ))]
    simp only [selectedBasePopulation, testedClasses, positiveClasses_baseCount]
  unfold center classProductMixture
  simp_rw [hw]
  let f : Classes K tick → ℝ := fun c =>
    (activeCounts allocation 1 c.1 c.2 : ℝ) /
      population allocation 1 (i.1.val.1.source, i.1.val.2) *
        (leftProbability side i c * rightProbability side i c)
  change (∑ c : testedClasses allocation i, f c.val) = _
  rw [Finset.sum_coe_sort]
  have hzero (c : Classes K tick) :
      (if 0 < activeCounts allocation 1 c.1 c.2 then f c else 0) = f c := by
    split_ifs with hc
    · rfl
    · have hz : activeCounts allocation 1 c.1 c.2 = 0 := Nat.eq_zero_of_not_pos hc
      simp [f, hz]
  simp only [testedClasses, positiveClasses, Finset.sum_filter, ite_and, hzero]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single i.1]
  · simp [f, parentCenter, leftProbability, rightProbability, leftSymbol, rightSymbol]
  · intro h hh
    apply Finset.sum_eq_zero
    intro u _
    exact ite_eq_right hh

def stageBActive (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    Active K tick := ⟨(.stageB h, phi), ht⟩

theorem stageB_leftLaw_branch (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (k : BSplit h) (side : Fin 3) (a : Fin 6) :
    leftLaw (stageBActive h phi ht) (branchShape (.stageB h, phi) k) side a =
      (littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) (phi.symm side) a : ℝ) := by
  change (placedChildLawRat (.stageB h, phi) (branchShape (.stageB h, phi) k)
    side false a : ℝ) = _
  rw [placedChildLawRat_branchShape (.stageB h, phi) k side false]
  simp [Work.childLaw, Work.splitShape, halfShape]

theorem stageB_rightLaw_branch (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (k : BSplit h) (side : Fin 3) (b : Fin 6) :
    rightLaw (stageBActive h phi ht) (branchShape (.stageB h, phi) k) side b =
      (littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩))
        (phi.symm side) b : ℝ) := by
  change (placedChildLawRat (.stageB h, phi) (branchShape (.stageB h, phi) k)
    side true b : ℝ) = _
  rw [placedChildLawRat_branchShape (.stageB h, phi) k side true]
  simp [Work.childLaw, Work.parentShape, Work.splitShape, halfShape]

theorem stageB_sum_laws (h : APositive K) (side : Fin 3) (a b : Fin 6) :
    (∑ k : BSplit h,
      stageBLaw (aShape h.val) (bSplit ⟨h, k, false⟩) *
        littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) side a *
        littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩)) side b) =
      halfLaw (aShape h.val) side (a, b) := by
  rw [halfLaw_positive_parent _ h.property]
  unfold positiveHalfLaw
  change (∑ k : Fin (below (aShape h.val)).length,
    stageBLaw (aShape h.val) (below (aShape h.val))[k.val] *
      littleLaw (aShape h.val) (below (aShape h.val))[k.val] side a *
      littleLaw (aShape h.val) (complement (aShape h.val) (below (aShape h.val))[k.val]) side b) = _
  exact Fin.sum_univ_fun_getElem (below (aShape h.val))
    (fun u => stageBLaw (aShape h.val) u * littleLaw (aShape h.val) u side a *
      littleLaw (aShape h.val) (complement (aShape h.val) u) side b)

theorem parentCenter_stageB (allocation : Allocation) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (side : Fin 3) (a b : Fin 6) :
    parentCenter allocation side (stageBActive h phi ht) a b =
      (halfLaw (aShape h.val) (phi.symm side) (a, b) : ℝ) := by
  let w : PlacedWork K := (.stageB h, phi)
  let f : JointPopulation.Shape → ℝ := fun u =>
    leftLaw (stageBActive h phi ht) u side a * rightLaw (stageBActive h phi ht) u side b
  calc
    parentCenter allocation side (stageBActive h phi ht) a b =
        (∑ u, (jointCounts allocation 1 w u : ℝ) * f u) /
          population allocation 1 (.afterA h.val, phi) := by
      unfold parentCenter
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [activeCounts, stageBActive, w, f, Work.source]
      ring
    _ = (∑ k : BSplit h, (branchPopulation allocation 1 w k : ℝ) * f (branchShape w k)) /
          population allocation 1 (.afterA h.val, phi) := by
      rw [jointCounts, shapeCounts_weighted_sum]
      rfl
    _ = ∑ k : BSplit h,
        (stageBLaw (aShape h.val) (bSplit ⟨h, k, false⟩) : ℝ) *
          (littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) (phi.symm side) a : ℝ) *
          (littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩))
            (phi.symm side) b : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [f, w]
      rw [stageB_leftLaw_branch, stageB_rightLaw_branch]
      rw [mul_div_right_comm,
        stageB_branchWeight_real allocation (by decide : 0 < (1 : ℕ)) h k phi]
      ring
    _ = (halfLaw (aShape h.val) (phi.symm side) (a, b) : ℝ) := by
      exact_mod_cast stageB_sum_laws h (phi.symm side) a b

theorem center_stageB (allocation : Allocation) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (side : Fin 3) (a b : SymbolChoice K tick) :
    center allocation side (stageBActive h phi ht, a, b) =
      (halfLaw (aShape h.val) (phi.symm side)
        (a (stageBActive h phi ht), b (stageBActive h phi ht)) : ℝ) := by
  rw [center_eq_parentCenter]
  exact parentCenter_stageB allocation h phi ht side _ _

end MatrixMultiplication.AllFieldHistoryMaskLaws

end

end OAI
