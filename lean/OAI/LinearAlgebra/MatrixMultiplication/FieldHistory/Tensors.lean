import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Geometry
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.ChildLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FiniteFamily

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation AllFieldParameters CWStrands InheritedMasks
open scoped BigOperators Classical

def ResidentStatistic {K : ℕ} : CanonicalHistory K → Type
  | .initial _ => PUnit
  | .afterA _ => PairSlot
  | .afterB _ | .partC _ => Fin 6
  | .afterC _ => PUnit

instance {K : ℕ} (h : CanonicalHistory K) : Fintype (ResidentStatistic h) := by
  cases h <;> dsimp [ResidentStatistic] <;> infer_instance

instance {K : ℕ} (h : CanonicalHistory K) : DecidableEq (ResidentStatistic h) := Classical.decEq _

def residentStatistic {K : ℕ} (h : CanonicalHistory K) :
    (Fin (currentLength h) → Fin 7) → ResidentStatistic h :=
  match h with
  | .initial _ => fun _ => PUnit.unit
  | .afterA _ => CWCompleteStatistics.fourStatistic
  | .afterB _ | .partC _ => CWCompleteStatistics.twoStatistic
  | .afterC _ => fun _ => PUnit.unit

def residentLawRat {K : ℕ} (h : CanonicalHistory K) (canonicalSide : Fin 3) :
    ResidentStatistic h → ℚ :=
  match h with
  | .initial _ => fun _ => 1
  | .afterA h => halfLaw (aShape h) canonicalSide
  | .afterB h => littleLaw (aShape h.1.val) (bShape h) canonicalSide
  | .partC h => littleLaw (cParameterParent h) (cShapeParent h) canonicalSide
  | .afterC _ => fun _ => 1

def residentLaw {K : ℕ} (h : History K) (physicalSide : Fin 3) :
    ResidentStatistic h.1 → ℝ :=
  fun a => residentLawRat h.1 (h.2.symm physicalSide) a

theorem residentLawRat_nonnegative {K : ℕ} (h : CanonicalHistory K) (side : Fin 3)
    (a : ResidentStatistic h) : 0 ≤ residentLawRat h side a := by
  cases h with
  | initial h => exact zero_le_one
  | afterA h => exact halfLaw_nonnegative (aShape h) side a
  | afterB h => exact littleLaw_nonnegative (aShape h.1.val) (bShape h) side a
  | partC h => exact littleLaw_nonnegative (cParameterParent h) (cShapeParent h) side a
  | afterC h => exact zero_le_one

theorem residentLawRat_normalized {K : ℕ} (h : CanonicalHistory K) (side : Fin 3) :
    ∑ a : ResidentStatistic h, residentLawRat h side a = 1 := by
  cases h with
  | initial h => exact Fintype.sum_unique (fun _ : PUnit => (1 : ℚ))
  | afterA h => exact halfLaw_normalized (aShape h) (aShape_size h) side
  | afterB h => exact littleLaw_normalized (aShape h.1.val) (bShape h) side
  | partC h => exact littleLaw_normalized (cParameterParent h) (cShapeParent h) side
  | afterC h => exact Fintype.sum_unique (fun _ : PUnit => (1 : ℚ))

def residentWidth {K : ℕ} (ε : ℝ) : CanonicalHistory K → ℝ
  | .initial _ => 0
  | .afterA _ => ε / 8
  | .afterB _ => ε / 128
  | .partC _ => ε / 256
  | .afterC _ => 0

abbrev HistoryWord {K : ℕ} (allocation : Allocation) (dilation : ℕ) (h : History K) :=
  Fin (population allocation dilation h) → Fin (currentLength h.1) → Fin 7

def residentMask {K : ℕ} (allocation : Allocation) (dilation : ℕ) (ε : ℝ)
    (h : History K) (side : Fin 3) (w : HistoryWord allocation dilation h) : Prop :=
  match h.1 with
  | .initial _ => True
  | .afterC _ => True
  | .afterA _ | .afterB _ | .partC _ =>
      0 < population allocation dilation h →
        typeWindow (residentLaw h side) (residentWidth ε h.1)
          (fun i => residentStatistic h.1 (w i))

theorem residentMask_zero_population {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (ε : ℝ) (h : History K) (hp : population allocation dilation h = 0)
    (side : Fin 3) (w : HistoryWord allocation dilation h) :
    residentMask allocation dilation ε h side w := by
  rcases h with ⟨h, phi⟩
  cases h <;> simp [residentMask, hp]

theorem residentWidth_mono {K : ℕ} {ε δ : ℝ} (hε : ε ≤ δ) (h : CanonicalHistory K) :
    residentWidth ε h ≤ residentWidth δ h := by
  cases h <;> simp only [residentWidth]
  all_goals first | exact le_rfl | exact div_le_div_of_nonneg_right hε (by norm_num)

theorem residentMask_mono {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    {ε δ : ℝ} (hε : ε ≤ δ) (h : History K) (side : Fin 3)
    (w : HistoryWord allocation dilation h)
    (hw : residentMask allocation dilation ε h side w) :
    residentMask allocation dilation δ h side w := by
  rcases h with ⟨h, phi⟩
  cases h <;> simp only [residentMask] at hw ⊢
  all_goals first
    | trivial
    | intro hp a
      exact le_trans (hw hp a) (residentWidth_mono hε _)

def historyTensor (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (h : History K) :
    Tensor F (HistoryWord allocation dilation h) (HistoryWord allocation dilation h)
      (HistoryWord allocation dilation h) :=
  ExactRecovery.delete
    (Tensor.power (shapeTensor (Fin (currentLength h.1)) (currentPhysicalShape h))
      (population allocation dilation h))
    (residentMask allocation dilation ε h 0) (residentMask allocation dilation ε h 1)
    (residentMask allocation dilation ε h 2)

def stateTensor (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (tick : ℕ) :
    Tensor F (∀ h : State K tick, HistoryWord allocation dilation h.val)
      (∀ h : State K tick, HistoryWord allocation dilation h.val)
      (∀ h : State K tick, HistoryWord allocation dilation h.val) :=
  CommonDimensions.familyProduct (fun h : State K tick =>
    historyTensor F allocation dilation ε h.val)

theorem historyTensor_support_shape (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (h : History K)
    (x y z : HistoryWord allocation dilation h)
    (hn : historyTensor F allocation dilation ε h x y z ≠ 0)
    (i : Fin (population allocation dilation h)) :
    weight (x i) = currentPhysicalShape h 0 ∧
      weight (y i) = currentPhysicalShape h 1 ∧
      weight (z i) = currentPhysicalShape h 2 := by
  apply shapeTensor_support (F := F) (currentPhysicalShape h) (x i) (y i) (z i)
  intro hz
  apply hn
  unfold historyTensor ExactRecovery.delete
  split_ifs
  · exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  · rfl

@[simp] theorem historyTensor_initial (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (h : Initial K) (phi : Placement) :
    historyTensor F allocation dilation ε (.initial h, phi) =
      Tensor.power (shapeTensor (Fin 8) (physicalShape phi (initialShape h)))
        (population allocation dilation (.initial h, phi)) := by
  funext x y z
  exact ite_eq_left ⟨trivial, trivial, trivial⟩

@[simp] theorem historyTensor_afterC (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (h : AfterC K) (phi : Placement) :
    historyTensor F allocation dilation ε (.afterC h, phi) =
      Tensor.power (shapeTensor (Fin 1) (physicalShape phi (cShape h)))
        (population allocation dilation (.afterC h, phi)) := by
  funext x y z
  exact ite_eq_left ⟨trivial, trivial, trivial⟩

end MatrixMultiplication.AllFieldHistory

end

end OAI
