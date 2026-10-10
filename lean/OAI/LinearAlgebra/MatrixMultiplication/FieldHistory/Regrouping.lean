import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRegrouping

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

abbrev StateWords (tick : ℕ) := ∀ h : State K tick, HistoryWord allocation m h.val
abbrev DueWords := ∀ h : DueState K tick, HistoryWord allocation m h.val.val
abbrev CarriedWords := ∀ h : Carried K tick, HistoryWord allocation m h.val.val
abbrev ActiveWords := ∀ h : Active K tick,
  HistoryWord allocation m (activeSourceEquiv h).val.val
abbrev ProducedWords := ∀ h : Produced K tick, HistoryWord allocation m h.val

instance dueWordsFintype : Fintype (DueWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : DueState K tick, HistoryWord allocation m h.val.val))

instance carriedWordsFintype : Fintype (CarriedWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : Carried K tick, HistoryWord allocation m h.val.val))

instance activeWordsFintype : Fintype (ActiveWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : Active K tick,
    HistoryWord allocation m (activeSourceEquiv h).val.val))

instance producedWordsFintype : Fintype (ProducedWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : Produced K tick, HistoryWord allocation m h.val))

def carriedTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (CarriedWords (K := K) (tick := tick) allocation m)
      (CarriedWords (K := K) (tick := tick) allocation m) (CarriedWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : Carried K tick =>
    historyTensor F allocation m ε h.val.val)

def activeTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (ActiveWords (K := K) (tick := tick) allocation m)
      (ActiveWords (K := K) (tick := tick) allocation m) (ActiveWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : Active K tick =>
    historyTensor F allocation m ε (activeSourceEquiv h).val.val)

def producedTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (ProducedWords (K := K) (tick := tick) allocation m)
      (ProducedWords (K := K) (tick := tick) allocation m) (ProducedWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : Produced K tick =>
    historyTensor F allocation m ε h.val)

def toState (x : DueWords (K := K) (tick := tick) allocation m ×
    CarriedWords (K := K) (tick := tick) allocation m) : StateWords (K := K) allocation m tick :=
  fun h => if hd : due tick h.val.1 then x.1 ⟨h, hd⟩ else x.2 ⟨h, hd⟩

@[simp] theorem toState_due
    (x : DueWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m)
    (h : DueState K tick) : toState (K := K) (tick := tick) allocation m x h.val = x.1 h := by
  simp only [toState, dite_eq_left h.property]

@[simp] theorem toState_carried
    (x : DueWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m)
    (h : Carried K tick) : toState (K := K) (tick := tick) allocation m x h.val = x.2 h := by
  simp only [toState, dite_eq_right h.property]

def dueTensorAt (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (DueWords (K := K) (tick := tick) allocation m)
      (DueWords (K := K) (tick := tick) allocation m) (DueWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : DueState K tick =>
    historyTensor F allocation m ε h.val.val)

theorem split_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : DueWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m) :
    stateTensor F (K := K) allocation m ε tick (toState (K := K) (tick := tick) allocation m x)
      (toState (K := K) (tick := tick) allocation m y) (toState (K := K) (tick := tick) allocation m z) =
    Tensor.product (dueTensorAt (K := K) (tick := tick) allocation m F ε) (carriedTensor (K := K) (tick := tick) allocation m F ε) x y z := by
  change (∏ h : State K tick, historyTensor F allocation m ε h.val
    (toState (K := K) (tick := tick) allocation m x h) (toState (K := K) (tick := tick) allocation m y h) (toState (K := K) (tick := tick) allocation m z h)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun h : State K tick => due tick h.val.1)]
  simp only [toState_due, toState_carried]
  rfl

def splitMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation m ε tick)
      (Tensor.product (dueTensorAt (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε)) where
  x := fun x s => if s = toState (K := K) (tick := tick) allocation m x then 1 else 0
  y := fun y s => if s = toState (K := K) (tick := tick) allocation m y then 1 else 0
  z := fun z s => if s = toState (K := K) (tick := tick) allocation m z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact split_coefficient allocation m F ε x y z

def toDue (x : ActiveWords (K := K) (tick := tick) allocation m) :
    DueWords (K := K) (tick := tick) allocation m :=
  Equiv.piCongrLeft (fun h : DueState K tick => HistoryWord allocation m h.val.val)
    activeSourceEquiv x

theorem active_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : ActiveWords (K := K) (tick := tick) allocation m) :
    dueTensorAt (K := K) (tick := tick) allocation m F ε (toDue (K := K) (tick := tick) allocation m x) (toDue (K := K) (tick := tick) allocation m y)
      (toDue (K := K) (tick := tick) allocation m z) = activeTensor (K := K) (tick := tick) allocation m F ε x y z := by
  change (∏ h : DueState K tick, historyTensor F allocation m ε h.val.val
    (toDue (K := K) (tick := tick) allocation m x h) (toDue (K := K) (tick := tick) allocation m y h) (toDue (K := K) (tick := tick) allocation m z h)) = _
  rw [← activeSourceEquiv.prod_comp]
  unfold toDue
  simp only [Equiv.piCongrLeft_apply_apply]
  rfl

def activeMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (dueTensorAt (K := K) (tick := tick) allocation m F ε)
      (activeTensor (K := K) (tick := tick) allocation m F ε) where
  x := fun x s => if s = toDue (K := K) (tick := tick) allocation m x then 1 else 0
  y := fun y s => if s = toDue (K := K) (tick := tick) allocation m y then 1 else 0
  z := fun z s => if s = toDue (K := K) (tick := tick) allocation m z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact active_coefficient allocation m F ε x y z

def activeCarriedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation m ε tick)
      (Tensor.product (activeTensor (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε)) :=
  (splitMap (K := K) (tick := tick) allocation m F ε).comp
    ((activeMap (K := K) (tick := tick) allocation m F ε).product
      (LocalMap.identity (carriedTensor (K := K) (tick := tick) allocation m F ε)))

def fromNext (x : StateWords (K := K) allocation m (tick + 1)) :
    ProducedWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m :=
  (fun h => x (stateTransition.symm (.inr h)),
    fun h => x (stateTransition.symm (.inl h)))

theorem next_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : StateWords (K := K) allocation m (tick + 1)) :
    Tensor.product (producedTensor (K := K) (tick := tick) allocation m F ε)
      (carriedTensor (K := K) (tick := tick) allocation m F ε) (fromNext (K := K) (tick := tick) allocation m x)
      (fromNext (K := K) (tick := tick) allocation m y) (fromNext (K := K) (tick := tick) allocation m z) =
    stateTensor F (K := K) allocation m ε (tick + 1) x y z := by
  change _ = ∏ h : State K (tick + 1), historyTensor F allocation m ε h.val
    (x h) (y h) (z h)
  rw [← stateTransition.symm.prod_comp]
  rw [Fintype.prod_sum_type]
  exact mul_comm _ _

def nextMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (Tensor.product (producedTensor (K := K) (tick := tick) allocation m F ε)
      (carriedTensor (K := K) (tick := tick) allocation m F ε))
      (stateTensor F (K := K) allocation m ε (tick + 1)) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (fromNext (K := K) (tick := tick) allocation m)
    (fromNext (K := K) (tick := tick) allocation m)
    (fromNext (K := K) (tick := tick) allocation m) _).symm.trans ?_⟩
  funext x y z
  exact next_coefficient allocation m F ε x y z

end MatrixMultiplication.AllFieldHistoryRegrouping

end

end OAI
