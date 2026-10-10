import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistorySums

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

private def aRelot {K L : ℕ} (lot : Fin L) (h : AfterA K) : AfterA L :=
  ⟨⟨(lot, h.1.val.2), h.1.property⟩, h.2⟩

private def bRelot {K L : ℕ} (lot : Fin L) (h : AfterB K) : AfterB L :=
  ⟨⟨aRelot lot h.1.val, h.1.property⟩, h.2⟩

private def partRelot {K L : ℕ} (lot : Fin L) (h : PartC K) : PartC L :=
  (⟨bRelot lot h.1.val, h.1.property⟩, h.2)

def workRelot {K L : ℕ} (lot : Fin L) : Work K → Work L
  | .stageA h => .stageA ⟨(lot, h.val.2), h.property⟩
  | .stageB h => .stageB ⟨aRelot lot h.val, h.property⟩
  | .stageC h => .stageC (partRelot lot h)

@[simp] theorem workRelot_lot {K L : ℕ} (lot : Fin L) (w : Work K) :
    (workRelot lot w).lot = lot := by cases w <;> rfl

@[simp] theorem workRelot_stage {K L : ℕ} (lot : Fin L) (w : Work K) :
    (workRelot lot w).stage = w.stage := by cases w <;> rfl

@[simp] theorem workRelot_self {K : ℕ} (w : Work K) : workRelot w.lot w = w := by
  cases w <;> rfl

@[simp] theorem workRelot_relot {K L M : ℕ} (first : Fin L) (last : Fin M)
    (w : Work K) : workRelot last (workRelot first w) = workRelot last w := by
  cases w <;> rfl

@[simp] theorem workAmount_relot {K L : ℕ} (allocation : Allocation)
    (lot : Fin L) (w : Work K) :
    workAmount allocation (workRelot lot w) = workAmount allocation w := by
  cases w <;> rfl

def workLotEquiv (K : ℕ) : Work K ≃ Fin K × Work 1 where
  toFun w := (w.lot, workRelot 0 w)
  invFun h := workRelot h.1 h.2
  left_inv w := by simp only [workRelot_relot, workRelot_self]
  right_inv h := by
    rcases h with ⟨lot, w⟩
    apply Prod.ext
    · exact workRelot_lot lot w
    · simp only [workRelot_relot]
      have hzero : (0 : Fin 1) = w.lot := Subsingleton.elim _ _
      rw [hzero, workRelot_self]

@[simp] theorem workLotEquiv_symm_apply (K : ℕ) (lot : Fin K) (w : Work 1) :
    (workLotEquiv K).symm (lot, w) = workRelot lot w := rfl

private def workStagesEquiv (K : ℕ) :
    Work K ≃ InitialPositive K ⊕ APositive K ⊕ PartC K where
  toFun
    | .stageA h => .inl h
    | .stageB h => .inr (.inl h)
    | .stageC h => .inr (.inr h)
  invFun
    | .inl h => .stageA h
    | .inr (.inl h) => .stageB h
    | .inr (.inr h) => .stageC h
  left_inv w := by cases w <;> rfl
  right_inv h := by rcases h with h | h | h <;> rfl

private theorem work_sum {K : ℕ} (f : Work K → ℝ) :
    (∑ w, f w) = (∑ h : InitialPositive K, f (.stageA h)) +
      (∑ h : APositive K, f (.stageB h)) + (∑ h : PartC K, f (.stageC h)) := by
  calc
    _ = ∑ h : InitialPositive K ⊕ APositive K ⊕ PartC K,
        f ((workStagesEquiv K).symm h) :=
      ((workStagesEquiv K).symm.sum_comp f).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      exact (add_assoc _ _ _).symm

theorem sum_lot_tick (K tick : ℕ) (stage : Fin 3) (value : ℝ) :
    (∑ lot : Fin K, if FiniteSchedule.lotTick lot stage = tick then value else 0) =
      if FiniteSchedule.stageActive K tick stage then value else 0 := by
  by_cases active : FiniteSchedule.stageActive K tick stage
  · obtain ⟨lot, hlot, unique⟩ :=
      (FiniteSchedule.stageActive_iff_unique_lot K tick stage).mp active
    have he (j : Fin K) : FiniteSchedule.lotTick j stage = tick ↔ j = lot :=
      ⟨unique j, fun h => by simpa only [h] using hlot⟩
    simp only [he, ite_eq_left active]
    simp
  · have hn (lot : Fin K) : FiniteSchedule.lotTick lot stage ≠ tick := by
      intro h
      exact active (h ▸ FiniteSchedule.lot_active_at_its_tick lot stage)
    simp only [hn, ite_eq_right active, ite_false, Finset.sum_const_zero]

def shapeValue {K : ℕ} (fA fB : Shape → ℝ)
    (fC : Shape → Shape → Fin 3 → ℝ) : Work K → ℝ
  | .stageA h => fA (initialShape h.val)
  | .stageB h => fB (aShape h.val)
  | .stageC h => fC (cParameterParent h) (cShapeParent h) h.2

@[simp] theorem shapeValue_relot {K L : ℕ} (fA fB : Shape → ℝ)
    (fC : Shape → Shape → Fin 3 → ℝ) (lot : Fin L) (w : Work K) :
    shapeValue fA fB fC (workRelot lot w) = shapeValue fA fB fC w := by
  cases w <;> rfl

def stageASourceSum (fA : Shape → ℝ) : ℝ :=
  (positiveInitial.map (fun g => (initialLaw g : ℝ) * fA g)).sum

def stageBSourceSum (fB : Shape → ℝ) : ℝ :=
  (positiveSecond.map (fun t => (secondMass t : ℝ) * fB t)).sum

def stageCSourceSum (allocation : Allocation) (fC : Shape → Shape → Fin 3 → ℝ) : ℝ :=
  (positiveSecond.map (fun t => (((below t).filter positive).map (fun u =>
    (littleMass t u : ℝ) * ∑ part : Fin 3, (allocation.mass part : ℝ) * fC t u part)).sum)).sum

theorem stageA_one_lot_sum (fA : Shape → ℝ) :
    (∑ h : InitialPositive 1, (initialAmount h.val : ℝ) * fA (initialShape h.val)) =
      stageASourceSum fA := by
  simpa only [Nat.cast_one, one_mul, initialAmount, stageASourceSum] using
    initial_positive_sum 1 (fun g => (initialLaw g : ℝ) * fA g)

theorem stageB_one_lot_sum (fB : Shape → ℝ) :
    (∑ h : APositive 1, (aAmount h.val : ℝ) * fB (aShape h.val)) =
      stageBSourceSum fB := by
  simpa only [Nat.cast_one, one_mul, stageBSourceSum] using a_positive_history_sum 1 fB

theorem stageC_one_lot_sum (allocation : Allocation) (fC : Shape → Shape → Fin 3 → ℝ) :
    (∑ h : PartC 1, (partAmount allocation h : ℝ) *
      fC (cParameterParent h) (cShapeParent h) h.2) = stageCSourceSum allocation fC := by
  simp only [Fintype.sum_prod_type, partAmount, Rat.cast_mul,
    cParameterParent, cShapeParent, mul_assoc, ← Finset.mul_sum]
  simpa only [Nat.cast_one, one_mul, stageCSourceSum] using
    b_positive_history_sum 1 (fun t u => ∑ part : Fin 3,
      (allocation.mass part : ℝ) * fC t u part)

private theorem subtype_sum_indicator_inline_MatrixMultiplication_AllFieldActiveSums {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] [Fintype {a // P a}] (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem active_shape_sum (K tick : ℕ) (allocation : Allocation)
    (fA fB : Shape → ℝ) (fC : Shape → Shape → Fin 3 → ℝ) :
    (∑ w : CanonicalActive K tick,
      workAmount allocation w.val * shapeValue fA fB fC w.val) =
      (if FiniteSchedule.stageActive K tick 0 then stageASourceSum fA else 0) +
      (if FiniteSchedule.stageActive K tick 1 then stageBSourceSum fB else 0) +
      (if FiniteSchedule.stageActive K tick 2 then stageCSourceSum allocation fC else 0) := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldActiveSums
    (fun w : Work K => FiniteSchedule.lotTick w.lot w.stage = tick)
    (fun w => workAmount allocation w * shapeValue fA fB fC w)]
  rw [← (workLotEquiv K).symm.sum_comp
    (fun w => if FiniteSchedule.lotTick w.lot w.stage = tick then
      workAmount allocation w * shapeValue fA fB fC w else 0)]
  simp only [Fintype.sum_prod_type, workLotEquiv_symm_apply, workRelot_lot,
    workRelot_stage, workAmount_relot, shapeValue_relot]
  rw [Finset.sum_comm]
  simp only [sum_lot_tick]
  rw [work_sum]
  change (∑ history : InitialPositive 1, if FiniteSchedule.stageActive K tick 0 then
    (initialAmount history.val : ℝ) * fA (initialShape history.val) else 0) +
    (∑ history : APositive 1, if FiniteSchedule.stageActive K tick 1 then
      (aAmount history.val : ℝ) * fB (aShape history.val) else 0) +
    (∑ history : PartC 1, if FiniteSchedule.stageActive K tick 2 then
      (partAmount allocation history : ℝ) *
        fC (cParameterParent history) (cShapeParent history) history.2 else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    stageA_one_lot_sum, stageB_one_lot_sum, stageC_one_lot_sum]

def shapeCapacity {K : ℕ} (fA fB : Shape → Staggering.Capacity)
    (fC : Shape → Shape → Fin 3 → Staggering.Capacity) (w : Work K) : Staggering.Capacity :=
  fun i => shapeValue (fun g => fA g i) (fun t => fB t i) (fun t u part => fC t u part i) w

def stageASourceCapacity (fA : Shape → Staggering.Capacity) : Staggering.Capacity :=
  fun i => stageASourceSum (fun g => fA g i)

def stageBSourceCapacity (fB : Shape → Staggering.Capacity) : Staggering.Capacity :=
  fun i => stageBSourceSum (fun t => fB t i)

def stageCSourceCapacity (allocation : Allocation)
    (fC : Shape → Shape → Fin 3 → Staggering.Capacity) : Staggering.Capacity :=
  fun i => stageCSourceSum allocation (fun t u part => fC t u part i)

theorem activeAggregateCapacity_shapeCapacity (K tick : ℕ) (allocation : Allocation)
    (fA fB : Shape → Staggering.Capacity)
    (fC : Shape → Shape → Fin 3 → Staggering.Capacity) :
    activeAggregateCapacity allocation tick (shapeCapacity (K := K) fA fB fC) =
      FiniteSchedule.tickCapacity K (stageASourceCapacity fA) (stageBSourceCapacity fB)
        (stageCSourceCapacity allocation fC) tick := by
  funext i
  exact active_shape_sum K tick allocation (fun g => fA g i) (fun t => fB t i)
    (fun t u part => fC t u part i)

end MatrixMultiplication.AllFieldHistory

end

end MatrixAllFields

end OAI
