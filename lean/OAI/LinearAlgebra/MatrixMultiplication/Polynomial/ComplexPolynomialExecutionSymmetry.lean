import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialKernelExecution

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Tensor

section Swap

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def swapXY (T : Tensor K X Y Z) : Tensor K Y X Z := fun y x z => T x y z

theorem RankAtMost.swapXY {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (swapXY T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, a, c, ?_⟩
  funext y x z
  simp only [rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem swapXY_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) :
    swapXY (restrict A B C T) = restrict B A C (swapXY T) := by
  funext y' x' z'
  simp only [swapXY, restrict]
  calc
    (∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T x y z) =
        ∑ y, ∑ x, ∑ z, A x' x * B y' y * C z' z * T x y z := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      ring

end Swap
end Tensor

namespace PolynomialLocalConstruction

open Tensor LocalMaps

variable {X Y Z OX OY OZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

theorem kernel_cyclic (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → Polynomial ℂ) (MY : Y → OY → AY → Polynomial ℂ)
    (MZ : Z → OZ → AZ → Polynomial ℂ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    kernel (Tensor.cyclic auxiliary) MY MZ MX y z x = kernel auxiliary MX MY MZ x y z := by
  have h := congrFun (congrFun (congrFun
    (Tensor.cyclic_restrict (MX x.1) (MY y.1) (MZ z.1)
      (fun a b c => Polynomial.C (auxiliary a b c))) y.2) z.2) x.2
  simpa only [kernel, fiberTransform, Tensor.cyclic, Tensor.restrict] using h.symm

theorem kernel_swapXY (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → Polynomial ℂ) (MY : Y → OY → AY → Polynomial ℂ)
    (MZ : Z → OZ → AZ → Polynomial ℂ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    kernel (Tensor.swapXY auxiliary) MY MX MZ y x z = kernel auxiliary MX MY MZ x y z := by
  have h := congrFun (congrFun (congrFun
    (Tensor.swapXY_restrict (MX x.1) (MY y.1) (MZ z.1)
      (fun a b c => Polynomial.C (auxiliary a b c))) y.2) x.2) z.2
  simpa only [kernel, fiberTransform, Tensor.swapXY, Tensor.restrict] using h.symm

end PolynomialLocalConstruction

namespace PolynomialKernelExecution.Execution

open Tensor PolynomialLocalConstruction

variable {X Y Z Prefix PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)

def cyclic : Execution Y Z X Prefix PY PZ PX AY AZ AX
    (fun y z x => support x y z) where
  auxiliary := Tensor.cyclic E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank.cyclic
  order := E.order
  leftDegree := E.middleDegree
  middleDegree := E.rightDegree
  rightDegree := E.leftDegree
  leftMap := E.middleMap
  middleMap := E.rightMap
  rightMap := E.leftMap
  left_degree := E.middle_degree
  middle_degree := E.right_degree
  right_degree := E.left_degree
  value := Tensor.cyclic E.value
  vanishes := by
    intro y z x hs j hj
    rw [kernel_cyclic]
    exact E.vanishes x y z hs j hj
  leading := by
    intro y z x hs
    rw [kernel_cyclic]
    exact E.leading x y z hs
  synchronized := by
    intro y z x hs hn
    have h := E.synchronized x y z hs hn
    exact ⟨h.1.symm.trans h.2, h.1.symm⟩

@[simp] theorem cyclic_auxiliary : E.cyclic.auxiliary = Tensor.cyclic E.auxiliary := rfl
@[simp] theorem cyclic_rankBound : E.cyclic.rankBound = E.rankBound := rfl
@[simp] theorem cyclic_order : E.cyclic.order = E.order := rfl
@[simp] theorem cyclic_leftDegree : E.cyclic.leftDegree = E.middleDegree := rfl
@[simp] theorem cyclic_middleDegree : E.cyclic.middleDegree = E.rightDegree := rfl
@[simp] theorem cyclic_rightDegree : E.cyclic.rightDegree = E.leftDegree := rfl
@[simp] theorem cyclic_leftMap : E.cyclic.leftMap = E.middleMap := rfl
@[simp] theorem cyclic_middleMap : E.cyclic.middleMap = E.rightMap := rfl
@[simp] theorem cyclic_rightMap : E.cyclic.rightMap = E.leftMap := rfl

@[simp] theorem cyclic_value
    (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) (x : X × (Prefix × PX)) :
    E.cyclic.value y z x = E.value x y z := rfl

theorem cyclic_kernel
    (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) (x : X × (Prefix × PX)) :
    kernel E.cyclic.auxiliary E.cyclic.leftMap E.cyclic.middleMap E.cyclic.rightMap y z x =
      kernel E.auxiliary E.leftMap E.middleMap E.rightMap x y z :=
  kernel_cyclic E.auxiliary E.leftMap E.middleMap E.rightMap x y z

def swapXY : Execution Y X Z Prefix PY PX PZ AY AX AZ
    (fun y x z => support x y z) where
  auxiliary := Tensor.swapXY E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank.swapXY
  order := E.order
  leftDegree := E.middleDegree
  middleDegree := E.leftDegree
  rightDegree := E.rightDegree
  leftMap := E.middleMap
  middleMap := E.leftMap
  rightMap := E.rightMap
  left_degree := E.middle_degree
  middle_degree := E.left_degree
  right_degree := E.right_degree
  value := Tensor.swapXY E.value
  vanishes := by
    intro y x z hs j hj
    rw [kernel_swapXY]
    exact E.vanishes x y z hs j hj
  leading := by
    intro y x z hs
    rw [kernel_swapXY]
    exact E.leading x y z hs
  synchronized := by
    intro y x z hs hn
    have h := E.synchronized x y z hs hn
    exact ⟨h.1.symm, h.1.symm.trans h.2⟩

@[simp] theorem swapXY_auxiliary : E.swapXY.auxiliary = Tensor.swapXY E.auxiliary := rfl
@[simp] theorem swapXY_rankBound : E.swapXY.rankBound = E.rankBound := rfl
@[simp] theorem swapXY_order : E.swapXY.order = E.order := rfl
@[simp] theorem swapXY_leftDegree : E.swapXY.leftDegree = E.middleDegree := rfl
@[simp] theorem swapXY_middleDegree : E.swapXY.middleDegree = E.leftDegree := rfl
@[simp] theorem swapXY_rightDegree : E.swapXY.rightDegree = E.rightDegree := rfl
@[simp] theorem swapXY_leftMap : E.swapXY.leftMap = E.middleMap := rfl
@[simp] theorem swapXY_middleMap : E.swapXY.middleMap = E.leftMap := rfl
@[simp] theorem swapXY_rightMap : E.swapXY.rightMap = E.rightMap := rfl

@[simp] theorem swapXY_value
    (y : Y × (Prefix × PY)) (x : X × (Prefix × PX)) (z : Z × (Prefix × PZ)) :
    E.swapXY.value y x z = E.value x y z := rfl

theorem swapXY_kernel
    (y : Y × (Prefix × PY)) (x : X × (Prefix × PX)) (z : Z × (Prefix × PZ)) :
    kernel E.swapXY.auxiliary E.swapXY.leftMap E.swapXY.middleMap E.swapXY.rightMap y x z =
      kernel E.auxiliary E.leftMap E.middleMap E.rightMap x y z :=
  kernel_swapXY E.auxiliary E.leftMap E.middleMap E.rightMap x y z

section OriginalCoordinates

variable {X' Y' Z' : Type*}
variable (eX : X' ≃ X) (eY : Y' ≃ Y) (eZ : Z' ≃ Z)

def reindexOriginal : Execution X' Y' Z' Prefix PX PY PZ AX AY AZ
    (fun x y z => support (eX x) (eY y) (eZ z)) where
  auxiliary := E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank
  order := E.order
  leftDegree := E.leftDegree
  middleDegree := E.middleDegree
  rightDegree := E.rightDegree
  leftMap := fun x => E.leftMap (eX x)
  middleMap := fun y => E.middleMap (eY y)
  rightMap := fun z => E.rightMap (eZ z)
  left_degree := fun x => E.left_degree (eX x)
  middle_degree := fun y => E.middle_degree (eY y)
  right_degree := fun z => E.right_degree (eZ z)
  value := fun x y z => E.value (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2)
  vanishes := fun x y z hs j hj =>
    E.vanishes (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) hs j hj
  leading := fun x y z hs =>
    E.leading (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) hs
  synchronized := fun x y z hs hn =>
    E.synchronized (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) hs hn

@[simp] theorem reindexOriginal_auxiliary :
    (E.reindexOriginal eX eY eZ).auxiliary = E.auxiliary := rfl
@[simp] theorem reindexOriginal_rankBound :
    (E.reindexOriginal eX eY eZ).rankBound = E.rankBound := rfl
@[simp] theorem reindexOriginal_order :
    (E.reindexOriginal eX eY eZ).order = E.order := rfl
@[simp] theorem reindexOriginal_leftDegree :
    (E.reindexOriginal eX eY eZ).leftDegree = E.leftDegree := rfl
@[simp] theorem reindexOriginal_middleDegree :
    (E.reindexOriginal eX eY eZ).middleDegree = E.middleDegree := rfl
@[simp] theorem reindexOriginal_rightDegree :
    (E.reindexOriginal eX eY eZ).rightDegree = E.rightDegree := rfl
@[simp] theorem reindexOriginal_leftMap :
    (E.reindexOriginal eX eY eZ).leftMap = fun x => E.leftMap (eX x) := rfl
@[simp] theorem reindexOriginal_middleMap :
    (E.reindexOriginal eX eY eZ).middleMap = fun y => E.middleMap (eY y) := rfl
@[simp] theorem reindexOriginal_rightMap :
    (E.reindexOriginal eX eY eZ).rightMap = fun z => E.rightMap (eZ z) := rfl

@[simp] theorem reindexOriginal_value
    (x : X' × (Prefix × PX)) (y : Y' × (Prefix × PY)) (z : Z' × (Prefix × PZ)) :
    (E.reindexOriginal eX eY eZ).value x y z =
      E.value (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) := rfl

theorem reindexOriginal_kernel
    (x : X' × (Prefix × PX)) (y : Y' × (Prefix × PY)) (z : Z' × (Prefix × PZ)) :
    kernel (E.reindexOriginal eX eY eZ).auxiliary
        (E.reindexOriginal eX eY eZ).leftMap (E.reindexOriginal eX eY eZ).middleMap
        (E.reindexOriginal eX eY eZ).rightMap x y z =
      kernel E.auxiliary E.leftMap E.middleMap E.rightMap
        (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) := rfl

end OriginalCoordinates

section Support

variable (support' : X → Y → Z → Prop)
variable (h : ∀ x y z, support' x y z → support x y z)

def onSupport : Execution X Y Z Prefix PX PY PZ AX AY AZ support' where
  auxiliary := E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank
  order := E.order
  leftDegree := E.leftDegree
  middleDegree := E.middleDegree
  rightDegree := E.rightDegree
  leftMap := E.leftMap
  middleMap := E.middleMap
  rightMap := E.rightMap
  left_degree := E.left_degree
  middle_degree := E.middle_degree
  right_degree := E.right_degree
  value := E.value
  vanishes := fun x y z hs j hj => E.vanishes x y z (h x.1 y.1 z.1 hs) j hj
  leading := fun x y z hs => E.leading x y z (h x.1 y.1 z.1 hs)
  synchronized := fun x y z hs hn => E.synchronized x y z (h x.1 y.1 z.1 hs) hn

@[simp] theorem onSupport_auxiliary : (E.onSupport support' h).auxiliary = E.auxiliary := rfl
@[simp] theorem onSupport_rankBound : (E.onSupport support' h).rankBound = E.rankBound := rfl
@[simp] theorem onSupport_order : (E.onSupport support' h).order = E.order := rfl
@[simp] theorem onSupport_leftDegree : (E.onSupport support' h).leftDegree = E.leftDegree := rfl
@[simp] theorem onSupport_middleDegree : (E.onSupport support' h).middleDegree = E.middleDegree := rfl
@[simp] theorem onSupport_rightDegree : (E.onSupport support' h).rightDegree = E.rightDegree := rfl
@[simp] theorem onSupport_leftMap : (E.onSupport support' h).leftMap = E.leftMap := rfl
@[simp] theorem onSupport_middleMap : (E.onSupport support' h).middleMap = E.middleMap := rfl
@[simp] theorem onSupport_rightMap : (E.onSupport support' h).rightMap = E.rightMap := rfl
@[simp] theorem onSupport_value : (E.onSupport support' h).value = E.value := rfl

theorem onSupport_kernel
    (x : X × (Prefix × PX)) (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) :
    kernel (E.onSupport support' h).auxiliary (E.onSupport support' h).leftMap
        (E.onSupport support' h).middleMap (E.onSupport support' h).rightMap x y z =
      kernel E.auxiliary E.leftMap E.middleMap E.rightMap x y z := rfl

end Support

end PolynomialKernelExecution.Execution
end MatrixMultiplication.Foundation

end

end OAI
