import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.ChildLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Support
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.HistorySymmetry
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskAction

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open JointCanonicalization InheritedMasks PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Classes (K tick : ℕ) := Active K tick × JointPopulation.Shape

abbrev Positions (allocation : Allocation) (m : ℕ) (c : Classes K tick) :=
  Fin (activeCounts allocation m c.1 c.2)

abbrev Letters (c : Classes K tick) := Fin (activeHalfLength c.1) → Fin 7

abbrev Words (allocation : Allocation) (m : ℕ) :=
  CompleteWordPair (Positions (K := K) (tick := tick) allocation m) Letters Letters

noncomputable instance permutationsFintype (allocation : Allocation) (m : ℕ) :
    Fintype (HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) := by
  letI : DecidableEq (Classes K tick) := Classical.decEq _
  letI : ∀ c : Classes K tick, DecidableEq (Positions allocation m c) :=
    fun _ => Classical.decEq _
  letI : Fintype (Classes K tick) := inferInstance
  letI : ∀ c : Classes K tick, Fintype (Equiv.Perm (Positions allocation m c)) :=
    fun c => Equiv.instFintype
  letI : Fintype ((c : Classes K tick) → Equiv.Perm (Positions allocation m c)) :=
    Pi.instFintype
  change Fintype (((c : Classes K tick) → Equiv.Perm (Positions allocation m c)) ×
    ((c : Classes K tick) → Equiv.Perm (Positions allocation m c)))
  infer_instance

abbrev SymbolChoice (K tick : ℕ) := ∀ h : Active K tick, Statistic h

abbrev MaskIndex (K tick : ℕ) := Active K tick × SymbolChoice K tick × SymbolChoice K tick

def testedClasses (allocation : Allocation) (i : MaskIndex K tick) : Finset (Classes K tick) :=
  positiveClasses allocation i.1

def pairWidth (ε : ℝ) (h : Active K tick) : ℝ := ε / 16 ^ h.val.1.stage.val

def childWidth (ε : ℝ) (h : Active K tick) : ℝ := pairWidth ε h / 8

theorem pairWidth_pos {ε : ℝ} (hε : 0 < ε) (h : Active K tick) :
    0 < pairWidth ε h := by
  unfold pairWidth
  positivity

theorem childWidth_pos {ε : ℝ} (hε : 0 < ε) (h : Active K tick) :
    0 < childWidth ε h := div_pos (pairWidth_pos hε h) (by norm_num)

def classStatistic (c : Classes K tick) : Letters c → Statistic c.1 := statistic c.1

def leftSymbol (i : MaskIndex K tick) (c : Classes K tick) : Statistic c.1 := i.2.1 c.1

def rightSymbol (i : MaskIndex K tick) (c : Classes K tick) : Statistic c.1 := i.2.2 c.1

def leftProbability (side : Fin 3) (i : MaskIndex K tick) (c : Classes K tick) : ℝ :=
  leftLaw c.1 c.2 side (leftSymbol i c)

def rightProbability (side : Fin 3) (i : MaskIndex K tick) (c : Classes K tick) : ℝ :=
  rightLaw c.1 c.2 side (rightSymbol i c)

def center (allocation : Allocation) (side : Fin 3) (i : MaskIndex K tick) : ℝ :=
  classProductMixture (fun c : testedClasses allocation i => Positions allocation 1 c.val)
    (fun c => leftProbability side i c.val) (fun c => rightProbability side i c.val)

def passes (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m) : Prop :=
  ∀ i : MaskIndex K tick, ¬ selectedWordPairMaskBad (testedClasses allocation i)
    classStatistic classStatistic (leftSymbol i) (rightSymbol i)
    (pairWidth ε i.1) (center allocation side i) w

def childWindows (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m) : Prop :=
  HistorySymmetry.childWindows classStatistic classStatistic
    (activeLaw (activeCounts allocation m) (fun c => leftLaw c.1 c.2 side))
    (activeLaw (activeCounts allocation m) (fun c => rightLaw c.1 c.2 side))
    (activeWidth (activeCounts allocation m) (fun c => childWidth ε c.1))
    (activeWidth (activeCounts allocation m) (fun c => childWidth ε c.1)) w

def lossConstant (allocation : Allocation) (ε : ℝ) : ℝ :=
  ∑ i : MaskIndex K tick,
    1 / (2 * selectedBasePopulation allocation (testedClasses allocation i) *
      (pairWidth ε i.1) ^ 2)

theorem lossConstant_nonneg (allocation : Allocation) (ε : ℝ) :
    0 ≤ lossConstant (K := K) (tick := tick) allocation ε := by
  apply Finset.sum_nonneg
  intro i _
  change 0 ≤ 1 / (2 * (selectedBaseCount allocation (testedClasses allocation i) : ℝ) *
    (pairWidth ε i.1) ^ 2)
  exact div_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _))

end MatrixMultiplication.AllFieldHistoryMasks

end

end OAI
