import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Counts
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.HalfLaws
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWCompleteStatistics

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters CWStrands CWWindowedLeaves
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def Work.Statistic {K : ℕ} : Work K → Type
  | .stageA _ => PairSlot
  | .stageB _ => Fin 6
  | .stageC _ => PUnit

instance {K : ℕ} (w : Work K) : Fintype w.Statistic := by
  cases w <;> dsimp [Work.Statistic] <;> infer_instance

instance {K : ℕ} (w : Work K) : DecidableEq w.Statistic := Classical.decEq _

def Work.statistic {K : ℕ} (w : Work K) : Raw w.halfLength → w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.fourStatistic
  | .stageB _ => CWCompleteStatistics.twoStatistic
  | .stageC _ => fun _ => PUnit.unit

def Work.statisticWeight {K : ℕ} (w : Work K) : w.Statistic → ℕ :=
  match w with
  | .stageA _ => fun a => AllFieldParameters.statisticWeight a.1 +
      AllFieldParameters.statisticWeight a.2
  | .stageB _ => AllFieldParameters.statisticWeight
  | .stageC _ => fun _ => 0

theorem Work.statistic_weight {K : ℕ} (w : Work K) (hsharing : w.stage ≠ 2)
    (x : Raw w.halfLength) : CWStrands.weight x = w.statisticWeight (w.statistic x) := by
  cases w with
  | stageA h => exact CWCompleteStatistics.four_weight x
  | stageB h => exact CWCompleteStatistics.two_weight x
  | stageC h => exact False.elim (hsharing rfl)

def Work.childLaw {K : ℕ} (w : Work K) (u : Shape) (side : Fin 3) :
    w.Statistic → ℚ :=
  match w with
  | .stageA _ => halfLaw u side
  | .stageB h => littleLaw (aShape h.val) u side
  | .stageC _ => fun _ => 1

theorem Work.childLaw_nonnegative {K : ℕ} (w : Work K) (u : Shape)
    (side : Fin 3) (a : w.Statistic) : 0 ≤ w.childLaw u side a := by
  cases w with
  | stageA h => exact halfLaw_nonnegative u side a
  | stageB h => exact littleLaw_nonnegative (aShape h.val) u side a
  | stageC h => exact zero_le_one

theorem Work.childLaw_normalized {K : ℕ} (w : Work K) (u : Shape)
    (hu : u ∈ shapes (2 * w.halfLength)) (side : Fin 3) :
    ∑ a : w.Statistic, w.childLaw u side a = 1 := by
  cases w with
  | stageA h => exact halfLaw_normalized u hu side
  | stageB h => exact littleLaw_normalized (aShape h.val) u side
  | stageC h => exact Fintype.sum_unique (fun _ : PUnit => (1 : ℚ))

theorem Work.childLaw_outside_support {K : ℕ} (w : Work K) (hsharing : w.stage ≠ 2)
    (u : Shape) (hu : u ∈ shapes (2 * w.halfLength)) (side : Fin 3)
    (a : w.Statistic) (ha : w.statisticWeight a ≠ u side) : w.childLaw u side a = 0 := by
  cases w with
  | stageA h => exact halfLaw_outside_support u hu side a ha
  | stageB h =>
      have hbound : u side < 5 :=
        lt_of_le_of_lt (mem_shapes_bound hu side) (by norm_num [Work.halfLength])
      exact littleLaw_outside_support (aShape h.val) u side hbound a ha
  | stageC h => exact False.elim (hsharing rfl)

def canonicalChildShape {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape) : Shape :=
  fun i => decodeShape u (w.2 i)

@[simp] theorem canonicalChildShape_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) : canonicalChildShape w (branchShape w b) = w.1.splitShape b := by
  funext i
  simp [canonicalChildShape, branchShape, physicalShape]

theorem Work.halfShape_mem {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    halfShape w.parentShape (w.splitShape b) right ∈ shapes (2 * w.halfLength) := by
  cases w with
  | stageA h => exact aShape_size ⟨h, b, right⟩
  | stageB h => exact bShape_size ⟨h, b, right⟩
  | stageC h =>
      have hi := stageCAtom_mem (cShapeParent h) (bShape_size h.1.val) h.1.property b
      have hs := stageC_children_geometry (cShapeParent h)
        (bShape_size h.1.val) h.1.property (stageCAtom (cShapeParent h) b)
        hi
      have ht : shapeTotal (cShapeParent h) = 4 := mem_shapes_total (bShape_size h.1.val)
      cases right
      · change stageCAtom (cShapeParent h) b ∈ shapes 2
        simpa only [ht] using below_mem_shapes hi
      · change complement (cShapeParent h) (stageCAtom (cShapeParent h) b) ∈ shapes 2
        simpa only [ht] using below_mem_shapes hs.1

def placedChildLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (right : Bool) : w.1.Statistic → ℚ :=
  w.1.childLaw (halfShape w.1.parentShape (canonicalChildShape w u) right)
    (w.2.symm side)

def childLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) : w.1.Statistic → ℚ := placedChildLawRat w u side false

def rightChildLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) : w.1.Statistic → ℚ := placedChildLawRat w u side true

@[simp] theorem placedChildLawRat_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (right : Bool) :
    placedChildLawRat w (branchShape w b) side right =
      w.1.childLaw (halfShape w.1.parentShape (w.1.splitShape b) right)
        (w.2.symm side) := by
  simp only [placedChildLawRat, canonicalChildShape_branchShape]

theorem placedChildLawRat_nonnegative {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (side : Fin 3) (right : Bool) (a : w.1.Statistic) :
    0 ≤ placedChildLawRat w u side right a :=
  w.1.childLaw_nonnegative _ _ a

theorem placedChildLawRat_normalized_of_pos {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) (side : Fin 3) (right : Bool) :
    ∑ a : w.1.Statistic, placedChildLawRat w u side right a = 1 := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  simp only [placedChildLawRat_branchShape]
  exact w.1.childLaw_normalized _ (w.1.halfShape_mem b right) _

def childLaw {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (a : w.1.Statistic) : ℝ := childLawRat w u side a

def rightChildLaw {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (a : w.1.Statistic) : ℝ := rightChildLawRat w u side a

abbrev ActiveStatistic {K tick : ℕ} (h : Active K tick) := h.val.1.Statistic

def activeStatistic {K tick : ℕ} (h : Active K tick) :
    Raw (activeHalfLength h) → ActiveStatistic h := h.val.1.statistic

def leftChildLaw {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) : ActiveStatistic c.1 → ℝ :=
  childLaw c.1.val c.2 side

def rightClassChildLaw {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) : ActiveStatistic c.1 → ℝ :=
  rightChildLaw c.1.val c.2 side

theorem leftChildLaw_nonnegative {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) (a : ActiveStatistic c.1) :
    0 ≤ leftChildLaw side c a := by
  change (0 : ℝ) ≤ (placedChildLawRat c.1.val c.2 side false a : ℝ)
  exact_mod_cast placedChildLawRat_nonnegative c.1.val c.2 side false a

theorem rightClassChildLaw_nonnegative {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) (a : ActiveStatistic c.1) :
    0 ≤ rightClassChildLaw side c a := by
  change (0 : ℝ) ≤ (placedChildLawRat c.1.val c.2 side true a : ℝ)
  exact_mod_cast placedChildLawRat_nonnegative c.1.val c.2 side true a

theorem leftChildLaw_normalized_of_pos {K tick : ℕ} (allocation : Allocation)
    (dilation : ℕ) (side : Fin 3) (c : Active K tick × JointPopulation.Shape)
    (hc : 0 < activeCounts allocation dilation c.1 c.2) :
    ∑ a : ActiveStatistic c.1, leftChildLaw side c a = 1 := by
  change (∑ a : c.1.val.1.Statistic,
    (placedChildLawRat c.1.val c.2 side false a : ℝ)) = 1
  exact_mod_cast placedChildLawRat_normalized_of_pos allocation dilation
    c.1.val c.2 hc side false

theorem rightClassChildLaw_normalized_of_pos {K tick : ℕ} (allocation : Allocation)
    (dilation : ℕ) (side : Fin 3) (c : Active K tick × JointPopulation.Shape)
    (hc : 0 < activeCounts allocation dilation c.1 c.2) :
    ∑ a : ActiveStatistic c.1, rightClassChildLaw side c a = 1 := by
  change (∑ a : c.1.val.1.Statistic,
    (placedChildLawRat c.1.val c.2 side true a : ℝ)) = 1
  exact_mod_cast placedChildLawRat_normalized_of_pos allocation dilation
    c.1.val c.2 hc side true

end MatrixMultiplication.AllFieldHistory

namespace MatrixMultiplication.AllFieldHistoryChildLaws

open AllFieldHistory
open scoped BigOperators

abbrev Statistic {K tick : ℕ} (h : Active K tick) := ActiveStatistic h

abbrev statistic {K tick : ℕ} (h : Active K tick) :
    CWWindowedLeaves.Raw (activeHalfLength h) → Statistic h := activeStatistic h

abbrev leftLaw {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) : Statistic h → ℝ := childLaw h.val u side

abbrev rightLaw {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) : Statistic h → ℝ := rightChildLaw h.val u side

theorem leftLaw_nonnegative {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) (a : Statistic h) : 0 ≤ leftLaw h u side a :=
  leftChildLaw_nonnegative side (h, u) a

theorem rightLaw_nonnegative {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) (a : Statistic h) : 0 ≤ rightLaw h u side a :=
  rightClassChildLaw_nonnegative side (h, u) a

theorem leftLaw_normalized {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation dilation h u) (side : Fin 3) :
    ∑ a : Statistic h, leftLaw h u side a = 1 :=
  leftChildLaw_normalized_of_pos allocation dilation side (h, u) hu

theorem rightLaw_normalized {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation dilation h u) (side : Fin 3) :
    ∑ a : Statistic h, rightLaw h u side a = 1 :=
  rightClassChildLaw_normalized_of_pos allocation dilation side (h, u) hu

theorem singleton_typeWindow {P : Type*} [Fintype P] [DecidableEq P] [Nonempty P]
    (η : ℝ) (hη : 0 ≤ η) (w : P → PUnit) :
    InheritedMasks.typeWindow (fun _ : PUnit => 1) η w := by
  intro a
  have hcount : MatrixMultiplication.Foundation.wordPopulation w a = Fintype.card P := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun i => ⟨i, Subsingleton.elim _ _⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun i => rfl }
  have hpos : (0 : ℝ) < Fintype.card P := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  simpa only [InheritedMasks.empiricalLaw, hcount, div_self (ne_of_gt hpos),
    sub_self, abs_zero] using hη

end MatrixMultiplication.AllFieldHistoryChildLaws

end

end OAI
