import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.InitialState
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryRecoveryBudget

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryTickCarry

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryRegrouping
open scoped Classical
attribute [local instance] Classical.propDecidable Classical.decEq

section Distribution

variable {F : Type*} [Field F]

def distributeProduct
    {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (active : Tensor F X Y Z) (carried : Tensor F U V W)
    (J : Type) [Fintype J] :
    LocalMap (Tensor.product (Tensor.directSum (fun _ : J => active)) carried)
      (Tensor.directSum (fun _ : J => Tensor.product active carried)) where
  x := fun x s => if s = ((x.1, x.2.1), x.2.2) then 1 else 0
  y := fun y s => if s = ((y.1, y.2.1), y.2.2) then 1 else 0
  z := fun z s => if s = ((z.1, z.2.1), z.2.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp [Tensor.pullback, Tensor.directSum, Tensor.product, ite_mul]

end Distribution

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (F : Type*) [Field F] (ε : ℝ) {J : Type} [Fintype J]

def liftExecution
    (E : Execution
      (activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : J =>
        producedTensor (K := K) (tick := tick) allocation m F ε))) :
    Execution (stateTensor F (K := K) allocation m ε tick)
      (Tensor.directSum (fun _ : J =>
        stateTensor F (K := K) allocation m ε (tick + 1))) where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map :=
    ((activeCarriedMap (K := K) (tick := tick) allocation m F ε).parallelCopies E.Copies).comp
      ((LocalMap.replicationProduct
        (activeTensor (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε) E.Copies).comp
      ((E.map.product
        (LocalMap.identity (carriedTensor (K := K) (tick := tick) allocation m F ε))).comp
      ((distributeProduct
        (producedTensor (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε) J).comp
        ((nextMap (K := K) (tick := tick) allocation m F ε).parallelCopies J))))

@[simp] theorem liftExecution_copies
    (E : Execution
      (activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : J =>
        producedTensor (K := K) (tick := tick) allocation m F ε))) :
    (liftExecution allocation m F ε E).Copies = E.Copies := rfl

@[simp] theorem liftExecution_card_copies
    (E : Execution
      (activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : J =>
        producedTensor (K := K) (tick := tick) allocation m F ε))) :
    Fintype.card (liftExecution allocation m F ε E).Copies = Fintype.card E.Copies := rfl

end MatrixMultiplication.AllFieldHistoryTickCarry

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation
attribute [local instance] Classical.propDecidable Classical.decEq

def activeEquivOrders (K tick : ℕ) :
    Active K tick ≃ Σ sigma : Placement, ActiveOrder K tick sigma :=
  (Equiv.sigmaFiberEquiv (fun w : Active K tick => w.val.physicalOrder)).symm

def activeWordsEquivOrders {K tick : ℕ} (W : Active K tick → Type*) :
    (∀ h, W h) ≃ (∀ sigma : Placement, ∀ h : ActiveOrder K tick sigma, W h.val) where
  toFun x _ h := x h.val
  invFun x h := x h.val.physicalOrder ⟨h, rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext sigma h
    rcases h with ⟨h, hh⟩
    cases hh
    rfl

theorem prod_active_eq_prod_orders {K tick : ℕ} {M : Type*} [CommMonoid M]
    (f : Active K tick → M) :
    (∏ h, f h) = ∏ sigma : Placement, ∏ h : ActiveOrder K tick sigma, f h.val := by
  calc
    _ = ∏ h : (Σ sigma : Placement, ActiveOrder K tick sigma), f h.2.val :=
      Fintype.prod_equiv (activeEquivOrders K tick) _ _ (fun _ => rfl)
    _ = _ := Fintype.prod_sigma _

theorem familyProduct_active_eq_orders {K tick : ℕ} {F : Type*} [CommSemiring F]
    {X Y Z : Active K tick → Type*}
    (T : ∀ h, Tensor F (X h) (Y h) (Z h))
    (x : ∀ h, X h) (y : ∀ h, Y h) (z : ∀ h, Z h) :
    CommonDimensions.familyProduct T x y z =
      CommonDimensions.familyProduct
        (fun sigma : Placement => CommonDimensions.familyProduct
          (fun h : ActiveOrder K tick sigma => T h.val))
        (activeWordsEquivOrders X x) (activeWordsEquivOrders Y y)
        (activeWordsEquivOrders Z z) :=
  prod_active_eq_prod_orders (fun h => T h (x h) (y h) (z h))

namespace GroupAssignment

variable {I : Type*} {V E : I → Type*}

def side {V E : Type*} (a : JointExtraction.Assignment V V V E) (i : Fin 3) :
    V → Option E := (Matrix.vecCons (a.x) (Matrix.vecCons (a.y) (Matrix.vecCons (a.z) Matrix.vecEmpty))) i

def restorePhysical {V E : Type*} (sigma : Placement)
    (a : JointExtraction.Assignment V V V E) : JointExtraction.Assignment V V V E where
  x := side a (sigma.symm 0)
  y := side a (sigma.symm 1)
  z := side a (sigma.symm 2)

theorem side_restorePhysical {V E : Type*} (sigma : Placement)
    (a : JointExtraction.Assignment V V V E) (i : Fin 3) :
    side (restorePhysical sigma a) i = side a (sigma.symm i) := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

def collect (a : ∀ i, V i → Option (E i)) (v : ∀ i, V i) : Option (∀ i, E i) :=
  if h : ∃ e : ∀ i, E i, ∀ i, a i (v i) = some (e i) then
    some (Classical.choose h) else none

theorem collect_eq_some (a : ∀ i, V i → Option (E i)) (v : ∀ i, V i) (e : ∀ i, E i) :
    collect a v = some e ↔ ∀ i, a i (v i) = some (e i) := by
  unfold collect
  split_ifs with h
  · constructor
    · intro he i
      have heq := Option.some.inj he
      simpa only [heq] using Classical.choose_spec h i
    · intro he
      congr 1
      funext i
      exact Option.some.inj ((Classical.choose_spec h i).symm.trans (he i))
  · constructor
    · intro he
      cases he
    · intro he
      exact False.elim (h ⟨e, he⟩)

theorem collect_failure_iff (a : ∀ i, V i → Option (E i))
    (v : ∀ i, V i) (e : ∀ i, E i) :
    collect a v ≠ some e ↔ ∃ i, a i (v i) ≠ some (e i) := by
  rw [ne_eq, collect_eq_some, not_forall]

variable {X Y Z : I → Type*}

def product (a : ∀ i, JointExtraction.Assignment (X i) (Y i) (Z i) (E i)) :
    JointExtraction.Assignment (∀ i, X i) (∀ i, Y i) (∀ i, Z i) (∀ i, E i) where
  x := collect (fun i => (a i).x)
  y := collect (fun i => (a i).y)
  z := collect (fun i => (a i).z)

variable [Fintype I] {F : Type*} [CommSemiring F]

theorem product_coherent (T : ∀ i, Tensor F (X i) (Y i) (Z i))
    (a : ∀ i, JointExtraction.Assignment (X i) (Y i) (Z i) (E i))
    (ha : ∀ i, JointExtraction.Coherent (T i) (a i)) :
    JointExtraction.Coherent (CommonDimensions.familyProduct T) (product a) := by
  intro x y z e f g hT hx hy hz
  have hx' := (collect_eq_some (fun i => (a i).x) x e).mp hx
  have hy' := (collect_eq_some (fun i => (a i).y) y f).mp hy
  have hz' := (collect_eq_some (fun i => (a i).z) z g).mp hz
  have hfactor (i : I) : T i (x i) (y i) (z i) ≠ 0 := by
    intro hi
    exact hT (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  constructor
  · funext i
    exact (ha i (x i) (y i) (z i) (e i) (f i) (g i)
      (hfactor i) (hx' i) (hy' i) (hz' i)).1
  · funext i
    exact (ha i (x i) (y i) (z i) (e i) (f i) (g i)
      (hfactor i) (hx' i) (hy' i) (hz' i)).2

theorem product_branch (T : ∀ i, Tensor F (X i) (Y i) (Z i))
    (a : ∀ i, JointExtraction.Assignment (X i) (Y i) (Z i) (E i))
    (e : ∀ i, E i) (x : ∀ i, X i) (y : ∀ i, Y i) (z : ∀ i, Z i) :
    JointExtraction.branch (CommonDimensions.familyProduct T) (product a) e x y z =
      ∏ i, JointExtraction.branch (T i) (a i) (e i) (x i) (y i) (z i) := by
  simp only [JointExtraction.branch, product, CommonDimensions.familyProduct,
    collect_eq_some]
  by_cases h : ∀ i, (a i).x (x i) = some (e i) ∧
      (a i).y (y i) = some (e i) ∧ (a i).z (z i) = some (e i)
  · have ho : (∀ i, (a i).x (x i) = some (e i)) ∧
        (∀ i, (a i).y (y i) = some (e i)) ∧
          (∀ i, (a i).z (z i) = some (e i)) :=
      ⟨fun i => (h i).1, fun i => (h i).2.1, fun i => (h i).2.2⟩
    rw [ite_eq_left ho]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (h i)]
  · have ho : ¬((∀ i, (a i).x (x i) = some (e i)) ∧
        (∀ i, (a i).y (y i) = some (e i)) ∧
          (∀ i, (a i).z (z i) = some (e i))) := by
      intro hh
      exact h (fun i => ⟨hh.1 i, hh.2.1 i, hh.2.2 i⟩)
    rw [ite_eq_right ho]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

end GroupAssignment

variable {K tick : ℕ}

def groupedSideAssignment (W : Active K tick → Type*) (E : Placement → Type*)
    (a : ∀ sigma, (∀ h : ActiveOrder K tick sigma, W h.val) → Option (E sigma))
    (x : ∀ h, W h) : Option (∀ sigma, E sigma) :=
  GroupAssignment.collect a (activeWordsEquivOrders W x)

theorem groupedSideAssignment_eq_some (W : Active K tick → Type*) (E : Placement → Type*)
    (a : ∀ sigma, (∀ h : ActiveOrder K tick sigma, W h.val) → Option (E sigma))
    (x : ∀ h, W h) (e : ∀ sigma, E sigma) :
    groupedSideAssignment W E a x = some e ↔
      ∀ sigma, a sigma (fun h => x h.val) = some (e sigma) :=
  GroupAssignment.collect_eq_some _ _ _

def groupedAssignment (X Y Z : Active K tick → Type*) (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (∀ h : ActiveOrder K tick sigma, X h.val)
      (∀ h : ActiveOrder K tick sigma, Y h.val)
      (∀ h : ActiveOrder K tick sigma, Z h.val) (E sigma)) :
    JointExtraction.Assignment (∀ h, X h) (∀ h, Y h) (∀ h, Z h) (∀ sigma, E sigma) where
  x := groupedSideAssignment X E (fun sigma => (a sigma).x)
  y := groupedSideAssignment Y E (fun sigma => (a sigma).y)
  z := groupedSideAssignment Z E (fun sigma => (a sigma).z)

theorem groupedAssignment_coherent {F : Type*} [CommSemiring F]
    (X Y Z : Active K tick → Type*) (E : Placement → Type*)
    (T : ∀ h, Tensor F (X h) (Y h) (Z h))
    (a : ∀ sigma, JointExtraction.Assignment
      (∀ h : ActiveOrder K tick sigma, X h.val)
      (∀ h : ActiveOrder K tick sigma, Y h.val)
      (∀ h : ActiveOrder K tick sigma, Z h.val) (E sigma))
    (ha : ∀ sigma, JointExtraction.Coherent
      (CommonDimensions.familyProduct (fun h : ActiveOrder K tick sigma => T h.val))
      (a sigma)) :
    JointExtraction.Coherent (CommonDimensions.familyProduct T)
      (groupedAssignment X Y Z E a) := by
  intro x y z e f g hT hx hy hz
  rw [familyProduct_active_eq_orders] at hT
  exact GroupAssignment.product_coherent _ a ha
    (activeWordsEquivOrders X x) (activeWordsEquivOrders Y y)
    (activeWordsEquivOrders Z z) e f g hT hx hy hz

theorem groupedAssignment_branch {F : Type*} [CommSemiring F]
    (X Y Z : Active K tick → Type*) (E : Placement → Type*)
    (T : ∀ h, Tensor F (X h) (Y h) (Z h))
    (a : ∀ sigma, JointExtraction.Assignment
      (∀ h : ActiveOrder K tick sigma, X h.val)
      (∀ h : ActiveOrder K tick sigma, Y h.val)
      (∀ h : ActiveOrder K tick sigma, Z h.val) (E sigma))
    (e : ∀ sigma, E sigma) (x : ∀ h, X h) (y : ∀ h, Y h) (z : ∀ h, Z h) :
    JointExtraction.branch (CommonDimensions.familyProduct T)
      (groupedAssignment X Y Z E a) e x y z =
        ∏ sigma : Placement, JointExtraction.branch
          (CommonDimensions.familyProduct (fun h : ActiveOrder K tick sigma => T h.val))
          (a sigma) (e sigma) (fun h => x h.val) (fun h => y h.val) (fun h => z h.val) := by
  calc
    _ = JointExtraction.branch
        (CommonDimensions.familyProduct (fun sigma : Placement =>
          CommonDimensions.familyProduct (fun h : ActiveOrder K tick sigma => T h.val)))
        (GroupAssignment.product a) e (activeWordsEquivOrders X x)
        (activeWordsEquivOrders Y y) (activeWordsEquivOrders Z z) := by
      simp only [JointExtraction.branch, groupedAssignment, groupedSideAssignment,
        GroupAssignment.product]
      rw [familyProduct_active_eq_orders T x y z]
      rfl
    _ = _ := GroupAssignment.product_branch _ a e _ _ _

def joinGroupTargets (counts : Active K tick → JointPopulation.Shape → ℕ)
    (e : ∀ sigma : Placement,
      JointPopulation.Target (fun h : ActiveOrder K tick sigma => counts h.val)) :
    JointPopulation.Target counts :=
  (activeWordsEquivOrders (fun h => MatrixMultiplication.Foundation.ExactWords (counts h))).symm e

@[simp] theorem joinGroupTargets_apply (counts : Active K tick → JointPopulation.Shape → ℕ)
    (e : ∀ sigma : Placement,
      JointPopulation.Target (fun h : ActiveOrder K tick sigma => counts h.val))
    (h : Active K tick) :
    joinGroupTargets counts e h = e h.val.physicalOrder ⟨h, rfl⟩ := rfl

@[simp] theorem joinGroupTargets_on_group
    (counts : Active K tick → JointPopulation.Shape → ℕ)
    (e : ∀ sigma : Placement,
      JointPopulation.Target (fun h : ActiveOrder K tick sigma => counts h.val))
    (sigma : Placement) (h : ActiveOrder K tick sigma) :
    joinGroupTargets counts e h.val = e sigma h := by
  rcases h with ⟨h, hh⟩
  cases hh
  rfl

theorem joinGroupTargets_injective (counts : Active K tick → JointPopulation.Shape → ℕ) :
    Function.Injective (joinGroupTargets counts) :=
  (activeWordsEquivOrders (fun h => MatrixMultiplication.Foundation.ExactWords (counts h))).symm.injective

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryMasks AllFieldHistoryRawMasks AllFieldHistoryIncomingMasks
open JointPopulation JointCanonicalization JointCanonicalCW InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def groupCounts (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) : JointPopulation.Shape → ℕ :=
  activeCounts allocation m h.val

abbrev GroupRaw (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  RawPairs (groupCounts (K := K) (tick := tick) allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)

def projectRaw (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    GroupRaw (K := K) (tick := tick) allocation m sigma := fun h j => w h.val j

def marginal (allocation : Allocation) (m : ℕ) (side : Fin 3) (sigma : Placement)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (h : ActiveOrder K tick sigma) a,
    wordPopulation (fun j => coarse activeHalfLength activeHalfLength
      AllFieldHistoryRecovery.halfLength_le_eight side h.val (w h j)) a =
    wordPopulation (sideWord (activeCounts allocation m) side
      (triple (activeCounts allocation m) (canonicalTarget (activeCounts allocation m))) h.val) a

def incoming (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) :
    HistoryWord allocation m (h.val.val.1.source, h.val.val.2) :=
  fun p => joinHalves h.val.val.1
    (w h ((sourcePositionsEquiv allocation m h.val).symm p))

def received (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ h : ActiveOrder K tick sigma,
    residentMask allocation m ε (h.val.val.1.source, h.val.val.2) side
      (incoming allocation m sigma h w)

def rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (i : MaskIndex K tick) (hi : i.1.val.physicalOrder = sigma),
    |(∑ j : JointPopulation.Positions (activeCounts allocation m) i.1,
        if statistic i.1 (w ⟨i.1, hi⟩ j).1 = i.2.1 i.1 ∧
          statistic i.1 (w ⟨i.1, hi⟩ j).2 = i.2.2 i.1 then (1 : ℝ) else 0) /
        (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) -
      center allocation side i| ≤ pairWidth ε i.1

def completeKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  marginal allocation m side sigma w ∧ received allocation m ε side sigma w ∧
    rawPass allocation m ε side sigma w

theorem marginal_project (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength AllFieldHistoryRecovery.halfLength_le_eight side w)
    (sigma : Placement) : marginal allocation m side sigma (projectRaw allocation m sigma w) := by
  intro h a
  exact hw h.val a

theorem received_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryIncomingMasks.received allocation m ε side w)
    (sigma : Placement) : received allocation m ε side sigma (projectRaw allocation m sigma w) := by
  intro h
  exact hw h.val

theorem rawPass_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRawMasks.rawPass allocation m ε side w)
    (sigma : Placement) : rawPass allocation m ε side sigma (projectRaw allocation m sigma w) := by
  intro i hi
  exact hw i

theorem completeKeep_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.completeKeep allocation m ε side w)
    (sigma : Placement) : completeKeep allocation m ε side sigma
      (projectRaw allocation m sigma w) :=
  ⟨marginal_project allocation m side w hw.1 sigma,
    received_project allocation m ε side w hw.2.1 sigma,
    rawPass_project allocation m ε side w hw.2.2 sigma⟩

theorem completeKeep_iff_all_groups (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.completeKeep allocation m ε side w ↔
      ∀ sigma, completeKeep allocation m ε side sigma (projectRaw allocation m sigma w) := by
  refine ⟨fun hw sigma => completeKeep_project allocation m ε side w hw sigma, ?_⟩
  intro hw
  refine ⟨?_, ?_, ?_⟩
  · intro h a
    exact (hw h.val.physicalOrder).1 ⟨h, rfl⟩ a
  · intro h
    exact (hw h.val.physicalOrder).2.1 ⟨h, rfl⟩
  · intro i
    exact (hw i.1.val.physicalOrder).2.2 i rfl

def groupRawSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (sigma : Placement) : Tensor F
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  sourceTensor (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => AllFieldHistoryRecovery.parents F h.val)

def groupPreparedSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (ε : ℝ) (sigma : Placement) : Tensor F
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  ExactRecovery.delete (groupRawSource F allocation m sigma)
    (completeKeep allocation m ε 0 sigma) (completeKeep allocation m ε 1 sigma)
    (completeKeep allocation m ε 2 sigma)

theorem rawSource_factor (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (x y z : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.rawSource F allocation m x y z =
      ∏ sigma : Placement, groupRawSource F allocation m sigma
        (projectRaw allocation m sigma x) (projectRaw allocation m sigma y)
        (projectRaw allocation m sigma z) :=
  prod_active_eq_prod_orders (fun h => ∏ j,
    AllFieldHistoryRecovery.parents F h (x h j) (y h j) (z h j))

theorem preparedSource_factor (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ)
    (x y z : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F allocation m)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 2) x y z =
      ∏ sigma : Placement, groupPreparedSource F allocation m ε sigma
        (projectRaw allocation m sigma x) (projectRaw allocation m sigma y)
        (projectRaw allocation m sigma z) := by
  have heq :
      (AllFieldHistoryRecovery.completeKeep allocation m ε 0 x ∧
        AllFieldHistoryRecovery.completeKeep allocation m ε 1 y ∧
        AllFieldHistoryRecovery.completeKeep allocation m ε 2 z) ↔
      ∀ sigma : Placement,
        completeKeep allocation m ε 0 sigma (projectRaw allocation m sigma x) ∧
        completeKeep allocation m ε 1 sigma (projectRaw allocation m sigma y) ∧
        completeKeep allocation m ε 2 sigma (projectRaw allocation m sigma z) := by
    rw [completeKeep_iff_all_groups, completeKeep_iff_all_groups, completeKeep_iff_all_groups]
    exact ⟨fun h sigma => ⟨h.1 sigma, h.2.1 sigma, h.2.2 sigma⟩,
      fun h => ⟨fun sigma => (h sigma).1, fun sigma => (h sigma).2.1,
        fun sigma => (h sigma).2.2⟩⟩
  by_cases h : AllFieldHistoryRecovery.completeKeep allocation m ε 0 x ∧
      AllFieldHistoryRecovery.completeKeep allocation m ε 1 y ∧
      AllFieldHistoryRecovery.completeKeep allocation m ε 2 z
  · rw [ExactRecovery.delete, ite_eq_left h, rawSource_factor]
    apply Finset.prod_congr rfl
    intro sigma _
    exact (ite_eq_left (heq.mp h sigma)).symm
  · rw [ExactRecovery.delete, ite_eq_right h]
    have hn : ¬∀ sigma : Placement,
        completeKeep allocation m ε 0 sigma (projectRaw allocation m sigma x) ∧
        completeKeep allocation m ε 1 sigma (projectRaw allocation m sigma y) ∧
        completeKeep allocation m ε 2 sigma (projectRaw allocation m sigma z) :=
      fun hh => h (heq.mpr hh)
    obtain ⟨sigma, hs⟩ := not_forall.mp hn
    exact (Finset.prod_eq_zero (Finset.mem_univ sigma) (ite_eq_right hs)).symm

end MatrixMultiplication.AllFieldHistoryGroupMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistorySource

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryRegrouping AllFieldHistoryIncomingMasks
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def deleteWithPred {F : Type*} [Field F] {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (source : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] :
    LocalMap source (ExactRecovery.delete source px py pz) := by
  let d := LocalMap.delete source px py pz
  refine ⟨d.x, d.y, d.z, d.coefficient.trans ?_⟩
  funext x y z
  unfold ExactRecovery.delete
  split_ifs <;> rfl

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

abbrev Raw := AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m

def toActive (w : Raw (K := K) (tick := tick) allocation m) :
    ActiveWords (K := K) (tick := tick) allocation m := fun h => incomingWord allocation m h w

theorem parent_coefficient (F : Type*) [Field F] (h : Active K tick)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    Tensor.power
      (CWStrands.shapeTensor (Fin (currentLength h.val.1.source))
        (currentPhysicalShape (h.val.1.source, h.val.2)))
      (population allocation m (h.val.1.source, h.val.2))
      (incomingWord allocation m h x) (incomingWord allocation m h y)
      (incomingWord allocation m h z) =
    ∏ i : JointPopulation.Positions (activeCounts allocation m) h,
      AllFieldHistoryRecovery.parents F h (x h i) (y h i) (z h i) := by
  change (∏ p : Fin (population allocation m (h.val.1.source, h.val.2)),
    CWStrands.shapeTensor _ _ (incomingWord allocation m h x p)
      (incomingWord allocation m h y p) (incomingWord allocation m h z p)) = _
  refine ((sourcePositionsEquiv allocation m h).prod_comp (fun p =>
    CWStrands.shapeTensor (Fin (currentLength h.val.1.source))
      (currentPhysicalShape (h.val.1.source, h.val.2))
      (incomingWord allocation m h x p) (incomingWord allocation m h y p)
      (incomingWord allocation m h z p))).symm.trans ?_
  apply Finset.prod_congr rfl
  intro i _
  simp only [incomingWord, Equiv.symm_apply_apply]
  erw [shapeTensor_joinHalves]
  unfold AllFieldHistoryRecovery.parents JointCanonicalMixed.inputTensor
  rw [ite_eq_left rfl]
  unfold JointCanonicalCW.parentTensor currentPhysicalShape
  rw [source_shape]
  rfl

def receivedSource (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F (K := K) (tick := tick) allocation m)
    (received allocation m ε 0) (received allocation m ε 1) (received allocation m ε 2)

theorem received_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    activeTensor (K := K) (tick := tick) allocation m F ε (toActive allocation m x) (toActive allocation m y)
      (toActive allocation m z) = receivedSource (K := K) (tick := tick) allocation m F ε x y z := by
  change (∏ h : Active K tick, historyTensor F allocation m ε
    (h.val.1.source, h.val.2) (incomingWord allocation m h x)
      (incomingWord allocation m h y) (incomingWord allocation m h z)) = _
  unfold receivedSource ExactRecovery.delete
  by_cases hp : received allocation m ε 0 x ∧ received allocation m ε 1 y ∧
      received allocation m ε 2 z
  · rw [ite_eq_left hp]
    change _ = ∏ h : Active K tick, ∏ i : JointPopulation.Positions (activeCounts allocation m) h,
      AllFieldHistoryRecovery.parents F h (x h i) (y h i) (z h i)
    apply Finset.prod_congr rfl
    intro h _
    unfold historyTensor ExactRecovery.delete
    rw [ite_eq_left ⟨hp.1 h, hp.2.1 h, hp.2.2 h⟩]
    exact parent_coefficient allocation m F h x y z
  · rw [ite_eq_right hp]
    have hh : ∃ h : Active K tick,
        ¬(residentMask allocation m ε (h.val.1.source, h.val.2) 0 (incomingWord allocation m h x) ∧
          residentMask allocation m ε (h.val.1.source, h.val.2) 1 (incomingWord allocation m h y) ∧
          residentMask allocation m ε (h.val.1.source, h.val.2) 2 (incomingWord allocation m h z)) := by
      by_contra hn
      apply hp
      push Not at hn
      exact ⟨fun h => (hn h).1, fun h => (hn h).2.1, fun h => (hn h).2.2⟩
    obtain ⟨h, hh⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ h)
    exact ite_eq_right hh

def receivedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (activeTensor (K := K) (tick := tick) allocation m F ε)
      (receivedSource (K := K) (tick := tick) allocation m F ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (toActive (K := K) (tick := tick) allocation m)
    (toActive (K := K) (tick := tick) allocation m)
    (toActive (K := K) (tick := tick) allocation m) _).symm.trans ?_⟩
  funext x y z
  exact received_coefficient allocation m F ε x y z

def marginal (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  JointCanonicalMixed.sideMask (activeCounts allocation m) activeHalfLength activeHalfLength
    AllFieldHistoryRecovery.halfLength_le_eight side w

def preparedSource (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (receivedSource (K := K) (tick := tick) allocation m F ε)
    (fun x => marginal (K := K) (tick := tick) allocation m 0 x ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 0 x)
    (fun y => marginal (K := K) (tick := tick) allocation m 1 y ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 1 y)
    (fun z => marginal (K := K) (tick := tick) allocation m 2 z ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 2 z)

theorem preparedSource_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    preparedSource (K := K) (tick := tick) allocation m F ε =
      ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F (K := K) (tick := tick) allocation m)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 2) := by
  funext x y z
  unfold preparedSource receivedSource marginal AllFieldHistoryRecovery.completeKeep
    ExactRecovery.delete
  split_ifs <;> simp_all only [and_true, true_and, not_false_eq_true]
  all_goals tauto

def preparedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (activeTensor (K := K) (tick := tick) allocation m F ε)
      (preparedSource (K := K) (tick := tick) allocation m F ε) :=
  (receivedMap (K := K) (tick := tick) allocation m F ε).comp (deleteWithPred (receivedSource (K := K) (tick := tick) allocation m F ε)
    (fun x => marginal (K := K) (tick := tick) allocation m 0 x ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 0 x)
    (fun y => marginal (K := K) (tick := tick) allocation m 1 y ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 1 y)
    (fun z => marginal (K := K) (tick := tick) allocation m 2 z ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 2 z))

abbrev GroupWords := ∀ sigma : Placement,
  AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma

def groupsEquiv : Raw (K := K) (tick := tick) allocation m ≃
    GroupWords (K := K) (tick := tick) allocation m :=
  activeWordsEquivOrders (fun h : Active K tick =>
    JointPopulation.Positions (activeCounts allocation m) h →
      ((Fin (activeHalfLength h) → Fin 7) × (Fin (activeHalfLength h) → Fin 7)))

@[simp] theorem project_groups_symm
    (x : GroupWords (K := K) (tick := tick) allocation m) (sigma : Placement) :
    AllFieldHistoryGroupMasks.projectRaw allocation m sigma
      ((groupsEquiv allocation m).symm x) = x sigma :=
  congrFun ((groupsEquiv allocation m).apply_symm_apply x) sigma

theorem grouped_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : GroupWords (K := K) (tick := tick) allocation m) :
    preparedSource (K := K) (tick := tick) allocation m F ε
      ((groupsEquiv allocation m).symm x) ((groupsEquiv allocation m).symm y)
      ((groupsEquiv allocation m).symm z) =
    CommonDimensions.familyProduct
      (fun sigma => AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma)
      x y z := by
  rw [preparedSource_eq_delete, AllFieldHistoryGroupMasks.preparedSource_factor]
  simp only [project_groups_symm, CommonDimensions.familyProduct]

def groupsMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (preparedSource (K := K) (tick := tick) allocation m F ε)
      (CommonDimensions.familyProduct (fun sigma : Placement =>
        AllFieldHistoryGroupMasks.groupPreparedSource F (K := K) (tick := tick)
          allocation m ε sigma)) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (groupsEquiv (K := K) (tick := tick) allocation m).symm
    (groupsEquiv (K := K) (tick := tick) allocation m).symm
    (groupsEquiv (K := K) (tick := tick) allocation m).symm _).symm.trans ?_⟩
  funext x y z
  exact grouped_coefficient allocation m F ε x y z

end MatrixMultiplication.AllFieldHistorySource

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev GroupTarget (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Target (groupCounts (K := K) (tick := tick) allocation m sigma)

def projectTarget (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m) :
    GroupTarget (K := K) (tick := tick) allocation m sigma := fun h => e h.val

def groupCoordinates (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : GroupTarget (K := K) (tick := tick) allocation m sigma) :=
  pairEquiv (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7) e

def groupCoarse {sigma : Placement} (side : Fin 3) (h : ActiveOrder K tick sigma)
    (w : (Fin (activeHalfLength h.val) → Fin 7) × (Fin (activeHalfLength h.val) → Fin 7)) :=
  coarse activeHalfLength activeHalfLength AllFieldHistoryRecovery.halfLength_le_eight
    side h.val w

def groupIdealSide (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (e : GroupTarget (K := K) (tick := tick) allocation m sigma)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  coarseMask (groupCounts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7) groupCoarse side e w ∧
    rawWindows (SL := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (SR := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (groupCounts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun c => statistic c.1.val) (fun c => statistic c.1.val)
      (fun c => leftLaw c.1.val c.2 side) (fun c => rightLaw c.1.val c.2 side)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val) e w

end MatrixMultiplication.AllFieldHistoryGroupedRecovery

end
end

end MatrixAllFields

end OAI
