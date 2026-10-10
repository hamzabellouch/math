import Mathlib
import OAI.LinearAlgebra.MatrixFields.Arithmetic.CommonDimensions
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryChildLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def due {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial h => initialShape h ∈ positiveInitial ∧ tick = h.1.val
  | .afterA h => aShape h ∈ positiveSecond ∧ tick = h.1.val.1.val + 1
  | .afterB _ => False
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 2
  | .afterC _ => False

def produced {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial _ => False
  | .afterA h => tick = h.1.val.1.val
  | .afterB h => tick = h.1.val.1.val.1.val + 1 ∧ positive (bShape h) ≠ true
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 1
  | .afterC h => tick = h.1.1.val.1.val.1.val.1.val + 2

abbrev Carried (K tick : ℕ) := {h : State K tick // ¬ due tick h.val.1}
abbrev Produced (K tick : ℕ) := {h : History K // produced tick h.1}

theorem produced_not_resident {K tick : ℕ} (h : CanonicalHistory K)
    (hp : produced tick h) : ¬ resident tick h := by
  cases h with
  | initial h => exact False.elim hp
  | afterA h => simp only [produced] at hp; simp only [resident]; omega
  | afterB h => simp only [produced] at hp; simp only [resident]; omega
  | partC h => simp only [produced] at hp; simp only [resident]; omega
  | afterC h => simp only [produced] at hp; simp only [resident]; omega

theorem resident_succ_iff {K tick : ℕ} (h : CanonicalHistory K) :
    resident (tick + 1) h ↔ (resident tick h ∧ ¬ due tick h) ∨ produced tick h := by
  cases h with
  | initial h =>
      by_cases hp : initialShape h ∈ positiveInitial
      · simp only [resident, due, produced, hp, true_implies, true_and, or_false]
        omega
      · simp [resident, due, produced, hp]
  | afterA h =>
      by_cases hp : aShape h ∈ positiveSecond
      · simp only [resident, due, produced, hp, true_implies, true_and]
        omega
      · simp only [resident, due, produced, hp, false_implies, and_true, false_and,
          not_false_eq_true]
        omega
  | afterB h =>
      by_cases hp : positive (bShape h) = true
      · simp [resident, due, produced, hp]
      · simp [resident, due, produced, hp, ne_eq]
        omega
  | partC h => simp only [resident, due, produced]; omega
  | afterC h => simp only [resident, due, produced, not_false_eq_true, and_true]; omega

def stateTransitionForward {K tick : ℕ} (h : State K (tick + 1)) :
    Carried K tick ⊕ Produced K tick := by
  by_cases hr : resident tick h.val.1
  · refine Sum.inl ⟨⟨h.val, hr⟩, ?_⟩
    rcases (resident_succ_iff h.val.1).mp h.property with hc | hp
    · exact hc.2
    · exact False.elim (produced_not_resident _ hp hr)
  · refine Sum.inr ⟨h.val, ?_⟩
    rcases (resident_succ_iff h.val.1).mp h.property with hc | hp
    · exact False.elim (hr hc.1)
    · exact hp

def stateTransitionBackward {K tick : ℕ} : Carried K tick ⊕ Produced K tick →
    State K (tick + 1)
  | .inl h => ⟨h.val.val, (resident_succ_iff _).mpr (.inl ⟨h.val.property, h.property⟩)⟩
  | .inr h => ⟨h.val, (resident_succ_iff _).mpr (.inr h.property)⟩

def stateTransition {K tick : ℕ} : State K (tick + 1) ≃ Carried K tick ⊕ Produced K tick where
  toFun := stateTransitionForward
  invFun := stateTransitionBackward
  left_inv h := by
    unfold stateTransitionForward
    split_ifs <;> rfl
  right_inv h := by
    cases h with
    | inl h => simp [stateTransitionForward, stateTransitionBackward, h.val.property]
    | inr h =>
        have hn := produced_not_resident h.val.1 h.property
        simp [stateTransitionForward, stateTransitionBackward, hn]

def productionParent {K tick : ℕ} (p : Produced K tick) : Active K tick := by
  rcases p with ⟨⟨h, phi⟩, hp⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h =>
      refine ⟨(.stageA h.1, phi), ?_⟩
      exact hp.symm
  | afterB h =>
      refine ⟨(.stageB h.1, phi), ?_⟩
      exact hp.1.symm
  | partC h =>
      refine ⟨(.stageB h.1.val.1, phi), ?_⟩
      exact hp.symm
  | afterC h =>
      refine ⟨(.stageC h.1, phi), ?_⟩
      exact hp.symm

abbrev DueState (K tick : ℕ) := {h : State K tick // due tick h.val.1}

def activeToDue {K tick : ℕ} (w : Active K tick) : DueState K tick := by
  refine ⟨⟨(w.val.1.source, w.val.2), ?_⟩, ?_⟩
  · exact Eq.mp (congrArg (fun n => resident n w.val.1.source) w.property)
      (work_source_resident w.val.1)
  · rcases w with ⟨⟨w, phi⟩, hw⟩
    cases w with
    | stageA h => exact ⟨h.property, hw.symm⟩
    | stageB h => exact ⟨h.property, hw.symm⟩
    | stageC h => exact hw.symm

def dueToActive {K tick : ℕ} (h : DueState K tick) : Active K tick := by
  rcases h with ⟨⟨⟨h, phi⟩, hr⟩, hd⟩
  cases h with
  | initial h => exact ⟨(.stageA ⟨h, hd.1⟩, phi), hd.2.symm⟩
  | afterA h => exact ⟨(.stageB ⟨h, hd.1⟩, phi), hd.2.symm⟩
  | afterB h => exact False.elim hd
  | partC h => exact ⟨(.stageC h, phi), hd.symm⟩
  | afterC h => exact False.elim hd

def activeSourceEquiv {K tick : ℕ} : Active K tick ≃ DueState K tick where
  toFun := activeToDue
  invFun := dueToActive
  left_inv w := by
    rcases w with ⟨⟨w, phi⟩, hw⟩
    cases w <;> rfl
  right_inv h := by
    rcases h with ⟨⟨⟨h, phi⟩, hr⟩, hd⟩
    cases h with
    | initial h => rfl
    | afterA h => rfl
    | afterB h => exact False.elim hd
    | partC h => rfl
    | afterC h => exact False.elim hd

def bSubdivisionPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : BPositive K) (phi : Placement) :
    Fin (population allocation dilation (.afterB h.val, phi)) ≃
      (Σ i : Fin 3, Fin (population allocation dilation (.partC (h, i), phi))) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma]
    exact (part_population_transition allocation dilation h phi).symm)

theorem final_state_terminal {K : ℕ} (h : State K (K + 2)) : terminal h.val.1 := by
  have hr := h.property
  have hlot := (initialAncestor h.val.1).1.isLt
  cases hh : h.val.1 with
  | initial g =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      intro hp
      have := hr hp
      omega
  | afterA a =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      intro hp
      have := hr.2 hp
      omega
  | afterB b =>
      simp only [hh, resident] at hr
      exact hr.2
  | partC c =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      omega
  | afterC c => trivial

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

def currentShape {K : ℕ} : CanonicalHistory K → Shape
  | .initial h => initialShape h
  | .afterA h => aShape h
  | .afterB h => bShape h
  | .partC h => cShapeParent h
  | .afterC h => cShape h

def currentLength {K : ℕ} : CanonicalHistory K → ℕ
  | .initial _ => 8
  | .afterA _ => 4
  | .afterB _ | .partC _ => 2
  | .afterC _ => 1

def currentPhysicalShape {K : ℕ} (h : History K) : Shape :=
  physicalShape h.2 (currentShape h.1)

theorem currentShape_spec {K : ℕ} (h : CanonicalHistory K) :
    ShapeBounded (currentShape h) ∧ shapeTotal (currentShape h) = 2 * currentLength h := by
  cases h with
  | initial h => exact root_shape_spec _ (initialShape_mem h)
  | afterA h => exact ⟨mem_shapes_bounded (aShape_size h) (by omega), mem_shapes_total (aShape_size h)⟩
  | afterB h => exact ⟨mem_shapes_bounded (bShape_size h) (by omega), mem_shapes_total (bShape_size h)⟩
  | partC h => exact ⟨mem_shapes_bounded (bShape_size h.1.val) (by omega),
      mem_shapes_total (bShape_size h.1.val)⟩
  | afterC h =>
      cases hh : h.2.2 with
      | false =>
          simpa only [currentShape, currentLength, cShape, cSplit, cShapeParent, halfShape, hh,
            Bool.false_eq_true, ite_false, Nat.mul_one] using
            stageC_shape_spec _ (bShape_size h.1.1.val) h.1.1.property h.2.1
      | true =>
          simpa only [currentShape, currentLength, cShape, cSplit, cShapeParent, halfShape, hh,
            ite_true, Nat.mul_one] using
            stageC_complement_spec _ (bShape_size h.1.1.val) h.1.1.property h.2.1

theorem currentPhysicalShape_total {K : ℕ} (h : History K) :
    shapeTotal (currentPhysicalShape h) = 2 * currentLength h.1 :=
  (physicalShape_total h.2 _).trans (currentShape_spec h.1).2

theorem positive_iff_no_zero (u : Shape) : positive u = true ↔ ∀ i, u i ≠ 0 := by
  simp only [positive, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    fin_cases i
    · change u 0 ≠ 0
      omega
    · change u 1 ≠ 0
      omega
    · change u 2 ≠ 0
      omega
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega

theorem not_positive_has_zero (u : Shape) (hu : positive u ≠ true) : ∃ i, u i = 0 := by
  by_contra hn
  apply hu
  rw [positive_iff_no_zero]
  intro i hi
  exact hn ⟨i, hi⟩

theorem terminal_has_zero {K : ℕ} (h : CanonicalHistory K) (ht : terminal h) :
    ∃ i, currentShape h i = 0 := by
  cases h with
  | initial h =>
      apply not_positive_has_zero
      intro hp
      exact ht (List.mem_filter.mpr ⟨initialShape_mem h, hp⟩)
  | afterA h =>
      apply not_positive_has_zero
      intro hp
      exact ht (List.mem_filter.mpr ⟨aShape_size h, hp⟩)
  | afterB h => exact not_positive_has_zero _ ht
  | partC h => exact False.elim ht
  | afterC h => exact cShape_zero h

theorem terminal_physical_zero {K : ℕ} (h : History K) (ht : terminal h.1) :
    ∃ s, currentPhysicalShape h s = 0 := by
  obtain ⟨i, hi⟩ := terminal_has_zero h.1 ht
  exact ⟨h.2 i, by simpa only [currentPhysicalShape, physicalShape_source] using hi⟩

theorem final_physical_zero {K : ℕ} (h : State K (K + 2)) :
    ∃ s, currentPhysicalShape h.val s = 0 :=
  terminal_physical_zero h.val (final_state_terminal h)

theorem source_shape {K : ℕ} (w : Work K) : currentShape w.source = w.parentShape := by
  cases w <;> rfl

theorem source_length {K : ℕ} (w : Work K) : currentLength w.source = 2 * w.halfLength := by
  cases w <;> rfl

theorem child_shape {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    currentShape (w.child b right) = halfShape w.parentShape (w.splitShape b) right := by
  cases w <;> rfl

theorem child_length {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    currentLength (w.child b right) = w.halfLength := by
  cases w <;> rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
  | initial h =>
      let : Unique (ResidentStatistic (.initial h)) := inferInstanceAs (Unique PUnit)
      exact Fintype.sum_unique _
  | afterA h => exact halfLaw_normalized (aShape h) (aShape_size h) side
  | afterB h => exact littleLaw_normalized (aShape h.1.val) (bShape h) side
  | partC h => exact littleLaw_normalized (cParameterParent h) (cShapeParent h) side
  | afterC h =>
      let : Unique (ResidentStatistic (.afterC h)) := inferInstanceAs (Unique PUnit)
      exact Fintype.sum_unique _

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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ProducedPositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  Σ h : Produced K tick, Fin (population allocation dilation h.val)

abbrev SplitPositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  Σ w : Active K tick, Σ b : w.val.1.Branch,
    Bool × Fin (branchPopulation allocation dilation w.val b)

def halfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation w b)) :
    Fin (population allocation dilation (w.1.child b right, w.2)) :=
  ⟨i.val, by rw [branchPopulation_half]; exact i.isLt⟩

def unhalfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (population allocation dilation (w.1.child b right, w.2))) :
    Fin (branchPopulation allocation dilation w b) :=
  ⟨i.val, by rw [← branchPopulation_half allocation dilation w b right]; exact i.isLt⟩

@[simp] theorem unhalf_halfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation w b)) :
    unhalfPosition allocation dilation w b right (halfPosition allocation dilation w b right i) = i := rfl

@[simp] theorem half_unhalfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (population allocation dilation (w.1.child b right, w.2))) :
    halfPosition allocation dilation w b right (unhalfPosition allocation dilation w b right i) = i := rfl

def splitToProduced {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    SplitPositions (K := K) (tick := tick) allocation dilation →
      ProducedPositions (K := K) (tick := tick) allocation dilation := by
  rintro ⟨⟨⟨w, phi⟩, hw⟩, b, right, i⟩
  cases w with
  | stageA h =>
      exact ⟨⟨(.afterA ⟨h, b, right⟩, phi), hw.symm⟩,
        halfPosition allocation dilation (.stageA h, phi) b right i⟩
  | stageB h =>
      let child : AfterB K := ⟨h, b, right⟩
      let j := halfPosition allocation dilation (.stageB h, phi) b right i
      by_cases hp : positive (bShape child) = true
      · let part := bSubdivisionPositionEquiv allocation dilation ⟨child, hp⟩ phi j
        exact ⟨⟨(.partC (⟨child, hp⟩, part.1), phi), hw.symm⟩, part.2⟩
      · exact ⟨⟨(.afterB child, phi), hw.symm, hp⟩, j⟩
  | stageC h =>
      exact ⟨⟨(.afterC (h, b, right), phi), hw.symm⟩,
        halfPosition allocation dilation (.stageC h, phi) b right i⟩

def producedToSplit {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    ProducedPositions (K := K) (tick := tick) allocation dilation →
      SplitPositions (K := K) (tick := tick) allocation dilation := by
  rintro ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h =>
      exact ⟨⟨(.stageA h.1, phi), hp.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageA h.1, phi) h.2.1 h.2.2 i⟩
  | afterB h =>
      exact ⟨⟨(.stageB h.1, phi), hp.1.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageB h.1, phi) h.2.1 h.2.2 i⟩
  | partC h =>
      let j := (bSubdivisionPositionEquiv allocation dilation h.1 phi).symm ⟨h.2, i⟩
      exact ⟨⟨(.stageB h.1.val.1, phi), hp.symm⟩, h.1.val.2.1, h.1.val.2.2,
        unhalfPosition allocation dilation (.stageB h.1.val.1, phi)
          h.1.val.2.1 h.1.val.2.2 j⟩
  | afterC h =>
      exact ⟨⟨(.stageC h.1, phi), hp.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageC h.1, phi) h.2.1 h.2.2 i⟩

theorem producedToSplit_splitToProduced {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation) :
    producedToSplit allocation dilation (splitToProduced allocation dilation p) = p := by
  rcases p with ⟨⟨⟨w, phi⟩, hw⟩, b, right, i⟩
  cases w with
  | stageA h => rfl
  | stageB h =>
      by_cases hp : positive (bShape (⟨h, b, right⟩ : AfterB K)) = true
      · dsimp only [splitToProduced]
        rw [dite_eq_left hp]
        dsimp only [producedToSplit]
        let lift : Fin (population allocation dilation (.afterB ⟨h, b, right⟩, phi)) →
            SplitPositions (K := K) (tick := tick) allocation dilation :=
          fun position => ⟨⟨(.stageB h, phi), hw⟩, b, right,
            unhalfPosition allocation dilation (.stageB h, phi) b right position⟩
        exact congrArg lift ((bSubdivisionPositionEquiv allocation dilation
          ⟨⟨h, b, right⟩, hp⟩ phi).symm_apply_apply
            (halfPosition allocation dilation (.stageB h, phi) b right i))
      · dsimp only [splitToProduced]
        rw [dite_eq_right hp]
        rfl
  | stageC h => rfl

theorem splitToProduced_producedToSplit {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    splitToProduced allocation dilation (producedToSplit allocation dilation p) = p := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h =>
      rcases h with ⟨a, b, right⟩
      dsimp only [producedToSplit, splitToProduced]
      rw [dite_eq_right hp.2]
      rfl
  | partC h =>
      rcases h with ⟨⟨⟨a, b, right⟩, hb⟩, part⟩
      dsimp only [producedToSplit, splitToProduced]
      rw [dite_eq_left hb]
      let lift : (Σ j : Fin 3,
          Fin (population allocation dilation
            (.partC (⟨⟨a, b, right⟩, hb⟩, j), phi))) →
          ProducedPositions (K := K) (tick := tick) allocation dilation :=
        fun q => ⟨⟨(.partC (⟨⟨a, b, right⟩, hb⟩, q.1), phi), hp⟩, q.2⟩
      exact congrArg lift ((bSubdivisionPositionEquiv allocation dilation
        ⟨⟨a, b, right⟩, hb⟩ phi).apply_symm_apply ⟨part, i⟩)
  | afterC h => rfl

def producedPositionEquiv {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    ProducedPositions (K := K) (tick := tick) allocation dilation ≃
      SplitPositions (K := K) (tick := tick) allocation dilation where
  toFun := producedToSplit allocation dilation
  invFun := splitToProduced allocation dilation
  left_inv := splitToProduced_producedToSplit allocation dilation
  right_inv := producedToSplit_splitToProduced allocation dilation

theorem producedPositionEquiv_parent {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    (producedPositionEquiv allocation dilation p).1 = productionParent p.1 := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

theorem producedPositionEquiv_shape {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    currentPhysicalShape p.1.val =
      physicalShape (producedPositionEquiv allocation dilation p).1.val.2
        (halfShape (producedPositionEquiv allocation dilation p).1.val.1.parentShape
          ((producedPositionEquiv allocation dilation p).1.val.1.splitShape
            (producedPositionEquiv allocation dilation p).2.1)
          (producedPositionEquiv allocation dilation p).2.2.1) := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

theorem producedPositionEquiv_length {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    currentLength p.1.val.1 = (producedPositionEquiv allocation dilation p).1.val.1.halfLength := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
