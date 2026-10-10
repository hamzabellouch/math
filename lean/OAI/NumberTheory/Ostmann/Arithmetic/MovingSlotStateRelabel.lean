import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalGiantWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotRelabel

namespace OAI

/-! # Evaluating the original recursion in finite pattern coordinates -/

namespace Ostmann
open scoped Classical

def MovingSlotState.map {σ τ : Type*} (f : σ → τ) (x : MovingSlotState σ) :
    MovingSlotState τ := ⟨x.depth, x.data.map f, x.leftGiant, x.rightGiant⟩

@[simp] theorem MovingSlotState.map_depth {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).depth = x.depth := rfl

@[simp] theorem MovingSlotState.map_data {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).data = x.data.map f := rfl

@[simp] theorem MovingSlotState.map_leftGiant {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).leftGiant = x.leftGiant := rfl

@[simp] theorem MovingSlotState.map_rightGiant {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).rightGiant = x.rightGiant := rfl

@[simp] theorem MovingSlotState.leftProduct_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).leftProduct value = x.leftProduct (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.leftProduct, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.rightProduct_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).rightProduct value = x.rightProduct (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.rightProduct, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.compensation_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).compensation value = x.compensation (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.compensation, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.child_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (b : Bool) (x : MovingSlotState σ) (P : ℕ) :
    (x.map f).child value b P = (x.child (value ∘ f) b P).map f := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> cases b <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.child, MovingSlotReversal.naturalProduct_map, Bool.false_eq_true,
    ite_true, ite_false] <;> rfl

@[simp] theorem movingSlotSystem_leftState_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ) (P : ℕ) :
    (movingSlotSystem value childBound pivotBound).leftState (x.map f) P =
      ((movingSlotSystem (value ∘ f) childBound pivotBound).leftState x P).map f :=
  MovingSlotState.child_map f value true x P

@[simp] theorem movingSlotSystem_rightState_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ) (P : ℕ) :
    (movingSlotSystem value childBound pivotBound).rightState (x.map f) P =
      ((movingSlotSystem (value ∘ f) childBound pivotBound).rightState x P).map f :=
  MovingSlotState.child_map f value false x P

@[simp] theorem movingHistoryPivot_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ)
    (s v w : ℤ) :
    historyPivot (movingSlotSystem value childBound pivotBound) (x.map f) s v w =
      historyPivot (movingSlotSystem (value ∘ f) childBound pivotBound) x s v w := by
  simp only [historyPivot, movingSlotSystem, MovingSlotState.leftProduct_map,
    MovingSlotState.rightProduct_map]

theorem movingValidTransferNode_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ)
    (s v w : ℤ) (P : ℕ) :
    ValidTransferNode (movingSlotSystem value childBound pivotBound) (x.map f) s v w P ↔
      ValidTransferNode (movingSlotSystem (value ∘ f) childBound pivotBound) x s v w P := by
  constructor <;> intro h
  all_goals refine ⟨h.root_ne_zero, ?_, ?_, h.pivot_pos, h.pivot_bound,
    h.left_bound, h.right_bound, ?_, h.pivot_unit⟩
  all_goals first
    | simpa only [movingSlotSystem, MovingSlotState.rightProduct_map] using h.root_unit
    | simpa only [movingSlotSystem, MovingSlotState.leftProduct_map,
        MovingSlotState.rightProduct_map] using h.relation
    | simpa only [movingSlotSystem, MovingSlotState.rightProduct_map,
        MovingSlotState.map_depth] using h.range_gap

/-- A relabeling evaluates every original pivot and guard, including the
integer division by the sampled compensation product. -/
theorem movingRecursiveWeight_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (leaf : MovingSlotState τ → ℤ → ℂ)
    (cutoff : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (x : MovingSlotState σ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) leaf cutoff n (x.map f) t =
      recursiveTransferWeight (movingSlotSystem (value ∘ f) childBound pivotBound)
        (fun x => leaf (x.map f)) (fun x => cutoff (x.map f)) n x t := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [recursiveTransferWeight, movingHistoryPivot_map, movingValidTransferNode_map]
    split_ifs
    · simp only [movingSlotSystem_leftState_map, movingSlotSystem_rightState_map]
      rw [ih, ih]
    · rfl

end Ostmann

end OAI
