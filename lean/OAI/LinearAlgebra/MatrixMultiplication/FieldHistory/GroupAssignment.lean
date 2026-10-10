import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Priority
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Extraction
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.CommonDimensions

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

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
    V → Option E := ![a.x, a.y, a.z] i

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
      apply -synthAssignedInstances @if_congr
      · rfl
      · exact familyProduct_active_eq_orders T x y z
      · rfl
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

end OAI
