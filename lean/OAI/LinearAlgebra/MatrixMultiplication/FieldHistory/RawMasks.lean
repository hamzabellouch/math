import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskCore

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRawMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open JointCanonicalization PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def rawPairCount (allocation : Allocation) (m : ℕ) (i : MaskIndex K tick)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : ℝ :=
  ∑ j : JointPopulation.Positions (activeCounts allocation m) i.1,
    if statistic i.1 (w i.1 j).1 = i.2.1 i.1 ∧
      statistic i.1 (w i.1 j).2 = i.2.2 i.1 then 1 else 0

def rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ i : MaskIndex K tick,
    |rawPairCount allocation m i w /
      (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) -
        center allocation side i| ≤ pairWidth ε i.1

theorem sum_positiveClasses (allocation : Allocation) (m : ℕ) (h : Active K tick)
    (f : ∀ c : Classes K tick, Positions allocation m c → ℝ) :
    (∑ c : positiveClasses allocation h, ∑ j, f c.val j) =
      ∑ u : JointPopulation.Shape, ∑ j, f (h, u) j := by
  have hzero (c : Classes K tick) (hc : ¬0 < activeCounts allocation 1 c.1 c.2) :
      (∑ j, f c j) = 0 := by
    have hcount : activeCounts allocation m c.1 c.2 = 0 := by
      rw [activeCounts_dilation, Nat.eq_zero_of_not_pos hc, mul_zero]
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val < 0 := by simpa only [hcount] using j.isLt
    exact (Nat.not_lt_zero _ hj).elim
  rw [Finset.sum_coe_sort (positiveClasses allocation h)
    (fun c : Classes K tick => ∑ j, f c j)]
  unfold positiveClasses
  rw [Finset.sum_filter]
  calc
    (∑ c : Classes K tick,
        if c.1 = h ∧ 0 < activeCounts allocation 1 c.1 c.2 then ∑ j, f c j else 0) =
        ∑ c : Classes K tick, if c.1 = h then ∑ j, f c j else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : 0 < activeCounts allocation 1 c.1 c.2
      · simp only [hc, and_true]
      · rw [hzero c hc]
        simp
    _ = ∑ u : JointPopulation.Shape, ∑ j, f (h, u) j := by
      rw [Fintype.sum_prod_type, Fintype.sum_eq_single h]
      · simp only [ite_true]
      · intro h' hh'
        apply Finset.sum_eq_zero
        intro u _
        exact ite_eq_right hh'

theorem selectedWordPairCount_pairEquiv (allocation : Allocation) (m : ℕ)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (i : MaskIndex K tick) (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    selectedWordPairCount (testedClasses allocation i)
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w)
      classStatistic classStatistic (leftSymbol i) (rightSymbol i) =
        rawPairCount allocation m i w := by
  let v : Words (K := K) (tick := tick) allocation m :=
    pairEquiv (activeCounts allocation m)
      (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w
  have hsum := sum_positiveClasses allocation m i.1 (fun c j =>
    if classStatistic c (v.left c j) = leftSymbol i c ∧
      classStatistic c (v.right c j) = rightSymbol i c then (1 : ℝ) else 0)
  unfold selectedWordPairCount
  rw [testedClasses, hsum]
  unfold rawPairCount
  rw [← Fintype.sum_sigma']
  apply Fintype.sum_equiv (positionEquiv (activeCounts allocation m) e i.1).symm
  rintro ⟨u, j⟩
  rfl

theorem testedClasses_populationSize (allocation : Allocation) (m : ℕ)
    (i : MaskIndex K tick) :
    populationSize (fun c : testedClasses allocation i => Positions allocation m c.val) =
      (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) := by
  change populationSize (selectedPositions allocation m (positiveClasses allocation i.1)) = _
  rw [positiveClasses_populationSize, population_dilation allocation m, Nat.cast_mul]
  exact mul_comm _ _

theorem raw_population_pos (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : Active K tick) :
    0 < (population allocation m (h.val.1.source, h.val.2) : ℝ) := by
  exact_mod_cast work_source_population_pos allocation hm h.val

theorem passes_pairEquiv_iff_rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    passes allocation m ε side
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w) ↔
      rawPass allocation m ε side w := by
  simp only [passes, selectedWordPairMaskBad, selectedWordPairCount_pairEquiv,
    testedClasses_populationSize, rawPass, not_lt]

theorem passes_pairEquiv_target_independent (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e f : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    passes allocation m ε side
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w) ↔
    passes allocation m ε side
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) f w) :=
  (passes_pairEquiv_iff_rawPass allocation m ε side e w).trans
    (passes_pairEquiv_iff_rawPass allocation m ε side f w).symm

end MatrixMultiplication.AllFieldHistoryRawMasks

end

end OAI
