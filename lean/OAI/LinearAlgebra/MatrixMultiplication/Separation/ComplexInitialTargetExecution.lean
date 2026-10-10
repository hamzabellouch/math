import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexInitialTargetKernel
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialKernelExecution

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.InitialTargetExecution

open Tensor LocalMaps PolynomialLocalConstruction PolynomialKernelExecution

variable {X Y Z RawLabel Label : Type*}

def scalarOutput : Label × Unit → Label × (Fin 1 × Fin 1) :=
  fun output => (output.1, (0, 0))

def initial (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (injective : Function.Injective embed)
    (support : X → Y → Z → Prop)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      lx x = ly y ∧ lx x = lz z) :
    Execution X Y Z Label Unit Unit Unit Unit Unit Unit support where
  auxiliary := InitialTargetKernel.auxiliary
  rankBound := 1
  auxiliary_rank := InitialTargetKernel.auxiliary_rank
  order := 0
  leftDegree := 0
  middleDegree := 0
  rightDegree := 0
  leftMap := fun x output input =>
    InitialTargetKernel.sideMap PX lx embed x (scalarOutput output) input
  middleMap := fun y output input =>
    InitialTargetKernel.sideMap PY ly embed y (scalarOutput output) input
  rightMap := fun z output input =>
    InitialTargetKernel.sideMap PZ lz embed z (scalarOutput output) input
  left_degree := fun x output input =>
    InitialTargetKernel.sideMap_degree PX lx embed x (scalarOutput output) input
  middle_degree := fun y output input =>
    InitialTargetKernel.sideMap_degree PY ly embed y (scalarOutput output) input
  right_degree := fun z output input =>
    InitialTargetKernel.sideMap_degree PZ lz embed z (scalarOutput output) input
  value := fun x y z => InitialTargetKernel.previousLeading PX PY PZ lx ly lz embed
    (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2)
  vanishes := fun x y z _ j hj =>
    InitialTargetKernel.kernel_low PX PY PZ lx ly lz embed
      (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2) j hj
  leading := fun x y z hs =>
    InitialTargetKernel.kernel_leading PX PY PZ lx ly lz embed injective support compatible
      (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2) hs
  synchronized := by
    intro x y z _ hn
    have h := (InitialTargetKernel.previousLeading_ne_zero_iff PX PY PZ lx ly lz embed
      (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2)).mp hn
    exact ⟨h.1, h.2.1⟩

variable (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
variable (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
variable (embed : Label → RawLabel) (injective : Function.Injective embed)
variable (support : X → Y → Z → Prop)
variable (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
  lx x = ly y ∧ lx x = lz z)

@[simp] theorem initial_rankBound :
    (initial PX PY PZ lx ly lz embed injective support compatible).rankBound = 1 := rfl

@[simp] theorem initial_order :
    (initial PX PY PZ lx ly lz embed injective support compatible).order = 0 := rfl

theorem initial_value_ne_zero_iff (x : X × (Label × Unit))
    (y : Y × (Label × Unit)) (z : Z × (Label × Unit)) :
    (initial PX PY PZ lx ly lz embed injective support compatible).value x y z ≠ 0 ↔
      x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        InitialTargetKernel.Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 :=
  InitialTargetKernel.previousLeading_ne_zero_iff PX PY PZ lx ly lz embed
    (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2)

theorem initial_eligible (x : X × (Label × Unit))
    (y : Y × (Label × Unit)) (z : Z × (Label × Unit))
    (hn : (initial PX PY PZ lx ly lz embed injective support compatible).value x y z ≠ 0) :
    InitialTargetKernel.Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 :=
  ((initial_value_ne_zero_iff PX PY PZ lx ly lz embed injective support compatible
    x y z).mp hn).2.2

theorem initial_substitution (original : Tensor ℂ X Y Z) :
    let E := initial PX PY PZ lx ly lz embed injective support compatible
    fiberTransform E.leftMap E.middleMap E.rightMap
        (fun x y z => Polynomial.C (Tensor.product original E.auxiliary x y z)) =
      originalScale (fun x y z => Polynomial.C (original x y z))
        (kernel E.auxiliary E.leftMap E.middleMap E.rightMap) := by
  let E := initial PX PY PZ lx ly lz embed injective support compatible
  have h := fiberTransform_originalScale E.leftMap E.middleMap E.rightMap
    (fun x y z => Polynomial.C (original x y z))
    (fun x y z => Polynomial.C (E.auxiliary x.2 y.2 z.2))
  have hinput :
      (fun x y z => Polynomial.C (Tensor.product original E.auxiliary x y z)) =
        originalScale (fun x y z => Polynomial.C (original x y z))
          (fun x y z => Polynomial.C (E.auxiliary x.2 y.2 z.2)) := by
    funext x y z
    simp only [Tensor.product, originalScale, map_mul]
  rw [← hinput] at h
  simpa only [E, kernel] using h

end MatrixMultiplication.Foundation.InitialTargetExecution

end

end OAI
