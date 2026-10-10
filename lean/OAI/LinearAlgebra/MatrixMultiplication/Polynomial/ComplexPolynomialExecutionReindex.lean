import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialKernelExecution

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution

open Tensor LocalMaps PolynomialLocalConstruction

variable {X Y Z Prefix PX PY PZ AX AY AZ Prefix' PX' PY' PZ' : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
variable (ePrefix : Prefix' ≃ Prefix) (eX : PX' ≃ PX) (eY : PY' ≃ PY) (eZ : PZ' ≃ PZ)

def reindexOutput : Execution X Y Z Prefix' PX' PY' PZ' AX AY AZ support where
  auxiliary := E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank
  order := E.order
  leftDegree := E.leftDegree
  middleDegree := E.middleDegree
  rightDegree := E.rightDegree
  leftMap := fun x output input => E.leftMap x (ePrefix output.1, eX output.2) input
  middleMap := fun y output input => E.middleMap y (ePrefix output.1, eY output.2) input
  rightMap := fun z output input => E.rightMap z (ePrefix output.1, eZ output.2) input
  left_degree := fun x output input =>
    E.left_degree x (ePrefix output.1, eX output.2) input
  middle_degree := fun y output input =>
    E.middle_degree y (ePrefix output.1, eY output.2) input
  right_degree := fun z output input =>
    E.right_degree z (ePrefix output.1, eZ output.2) input
  value := fun x y z => E.value
    (x.1, (ePrefix x.2.1, eX x.2.2))
    (y.1, (ePrefix y.2.1, eY y.2.2))
    (z.1, (ePrefix z.2.1, eZ z.2.2))
  vanishes := fun x y z hs j hj => E.vanishes
    (x.1, (ePrefix x.2.1, eX x.2.2))
    (y.1, (ePrefix y.2.1, eY y.2.2))
    (z.1, (ePrefix z.2.1, eZ z.2.2)) hs j hj
  leading := fun x y z hs => E.leading
    (x.1, (ePrefix x.2.1, eX x.2.2))
    (y.1, (ePrefix y.2.1, eY y.2.2))
    (z.1, (ePrefix z.2.1, eZ z.2.2)) hs
  synchronized := by
    intro x y z hs hn
    have h := E.synchronized
      (x.1, (ePrefix x.2.1, eX x.2.2))
      (y.1, (ePrefix y.2.1, eY y.2.2))
      (z.1, (ePrefix z.2.1, eZ z.2.2)) hs hn
    exact ⟨ePrefix.injective h.1, ePrefix.injective h.2⟩

@[simp] theorem reindexOutput_auxiliary :
    (E.reindexOutput ePrefix eX eY eZ).auxiliary = E.auxiliary := rfl

@[simp] theorem reindexOutput_rankBound :
    (E.reindexOutput ePrefix eX eY eZ).rankBound = E.rankBound := rfl

@[simp] theorem reindexOutput_order :
    (E.reindexOutput ePrefix eX eY eZ).order = E.order := rfl

@[simp] theorem reindexOutput_leftDegree :
    (E.reindexOutput ePrefix eX eY eZ).leftDegree = E.leftDegree := rfl

@[simp] theorem reindexOutput_middleDegree :
    (E.reindexOutput ePrefix eX eY eZ).middleDegree = E.middleDegree := rfl

@[simp] theorem reindexOutput_rightDegree :
    (E.reindexOutput ePrefix eX eY eZ).rightDegree = E.rightDegree := rfl

@[simp] theorem reindexOutput_leftMap (x : X) (output : Prefix' × PX') (input : AX) :
    (E.reindexOutput ePrefix eX eY eZ).leftMap x output input =
      E.leftMap x (ePrefix output.1, eX output.2) input := rfl

@[simp] theorem reindexOutput_middleMap (y : Y) (output : Prefix' × PY') (input : AY) :
    (E.reindexOutput ePrefix eX eY eZ).middleMap y output input =
      E.middleMap y (ePrefix output.1, eY output.2) input := rfl

@[simp] theorem reindexOutput_rightMap (z : Z) (output : Prefix' × PZ') (input : AZ) :
    (E.reindexOutput ePrefix eX eY eZ).rightMap z output input =
      E.rightMap z (ePrefix output.1, eZ output.2) input := rfl

@[simp] theorem reindexOutput_value
    (x : X × (Prefix' × PX')) (y : Y × (Prefix' × PY')) (z : Z × (Prefix' × PZ')) :
    (E.reindexOutput ePrefix eX eY eZ).value x y z = E.value
      (x.1, (ePrefix x.2.1, eX x.2.2))
      (y.1, (ePrefix y.2.1, eY y.2.2))
      (z.1, (ePrefix z.2.1, eZ z.2.2)) := rfl

@[simp] theorem reindexOutput_kernel
    (x : X × (Prefix' × PX')) (y : Y × (Prefix' × PY')) (z : Z × (Prefix' × PZ')) :
    kernel (E.reindexOutput ePrefix eX eY eZ).auxiliary
        (E.reindexOutput ePrefix eX eY eZ).leftMap
        (E.reindexOutput ePrefix eX eY eZ).middleMap
        (E.reindexOutput ePrefix eX eY eZ).rightMap x y z =
      kernel E.auxiliary E.leftMap E.middleMap E.rightMap
        (x.1, (ePrefix x.2.1, eX x.2.2))
        (y.1, (ePrefix y.2.1, eY y.2.2))
        (z.1, (ePrefix z.2.1, eZ z.2.2)) := rfl

theorem reindexOutput_fiberTransform
    (P : Tensor (Polynomial ℂ) (X × AX) (Y × AY) (Z × AZ))
    (x : X × (Prefix' × PX')) (y : Y × (Prefix' × PY')) (z : Z × (Prefix' × PZ')) :
    fiberTransform (E.reindexOutput ePrefix eX eY eZ).leftMap
        (E.reindexOutput ePrefix eX eY eZ).middleMap
        (E.reindexOutput ePrefix eX eY eZ).rightMap P x y z =
      fiberTransform E.leftMap E.middleMap E.rightMap P
        (x.1, (ePrefix x.2.1, eX x.2.2))
        (y.1, (ePrefix y.2.1, eY y.2.2))
        (z.1, (ePrefix z.2.1, eZ z.2.2)) := rfl

theorem reindexOutput_value_preimage
    (x : X × (Prefix × PX)) (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) :
    (E.reindexOutput ePrefix eX eY eZ).value
        (x.1, (ePrefix.symm x.2.1, eX.symm x.2.2))
        (y.1, (ePrefix.symm y.2.1, eY.symm y.2.2))
        (z.1, (ePrefix.symm z.2.1, eZ.symm z.2.2)) = E.value x y z := by
  simp only [reindexOutput_value, Equiv.apply_symm_apply]

theorem reindexOutput_kernel_preimage
    (x : X × (Prefix × PX)) (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) :
    kernel (E.reindexOutput ePrefix eX eY eZ).auxiliary
        (E.reindexOutput ePrefix eX eY eZ).leftMap
        (E.reindexOutput ePrefix eX eY eZ).middleMap
        (E.reindexOutput ePrefix eX eY eZ).rightMap
        (x.1, (ePrefix.symm x.2.1, eX.symm x.2.2))
        (y.1, (ePrefix.symm y.2.1, eY.symm y.2.2))
        (z.1, (ePrefix.symm z.2.1, eZ.symm z.2.2)) =
      kernel E.auxiliary E.leftMap E.middleMap E.rightMap x y z := by
  simp only [reindexOutput_kernel, Equiv.apply_symm_apply]

end MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution

end

end OAI
