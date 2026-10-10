import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialControlledKernel

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialKernelExecution

open Tensor PolynomialLocalConstruction PolynomialControlledKernel

variable {X Y Z Prefix PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

structure Execution (X Y Z Prefix PX PY PZ AX AY AZ : Type*)
    [Fintype AX] [Fintype AY] [Fintype AZ] (support : X → Y → Z → Prop) where
  auxiliary : Tensor ℂ AX AY AZ
  rankBound : ℕ
  auxiliary_rank : RankAtMost auxiliary rankBound
  order : ℕ
  leftDegree : ℕ
  middleDegree : ℕ
  rightDegree : ℕ
  leftMap : X → (Prefix × PX) → AX → Polynomial ℂ
  middleMap : Y → (Prefix × PY) → AY → Polynomial ℂ
  rightMap : Z → (Prefix × PZ) → AZ → Polynomial ℂ
  left_degree : ∀ x output input, (leftMap x output input).degree ≤ leftDegree
  middle_degree : ∀ y output input, (middleMap y output input).degree ≤ middleDegree
  right_degree : ∀ z output input, (rightMap z output input).degree ≤ rightDegree
  value : Tensor ℂ (X × (Prefix × PX)) (Y × (Prefix × PY)) (Z × (Prefix × PZ))
  vanishes : ∀ x y z, support x.1 y.1 z.1 → ∀ j < order,
    (kernel auxiliary leftMap middleMap rightMap x y z).coeff j = 0
  leading : ∀ x y z, support x.1 y.1 z.1 →
    (kernel auxiliary leftMap middleMap rightMap x y z).coeff order = value x y z
  synchronized : ∀ x y z, support x.1 y.1 z.1 → value x y z ≠ 0 →
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1

variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
variable {New NX NY NZ BX BY BZ : Type*}
variable [Fintype BX] [Fintype BY] [Fintype BZ]

structure Stage (New NX NY NZ BX BY BZ : Type*)
    [Fintype BX] [Fintype BY] [Fintype BZ] where
  auxiliary : Tensor ℂ BX BY BZ
  rankBound : ℕ
  auxiliary_rank : RankAtMost auxiliary rankBound
  order : ℕ
  leftDegree : ℕ
  middleDegree : ℕ
  rightDegree : ℕ
  leftMap : Prefix → X → (New × NX) → BX → Polynomial ℂ
  middleMap : Prefix → Y → (New × NY) → BY → Polynomial ℂ
  rightMap : Prefix → Z → (New × NZ) → BZ → Polynomial ℂ
  left_degree : ∀ prior x output input, (leftMap prior x output input).degree ≤ leftDegree
  middle_degree : ∀ prior y output input, (middleMap prior y output input).degree ≤ middleDegree
  right_degree : ∀ prior z output input, (rightMap prior z output input).degree ≤ rightDegree
  eligible : Prefix → X → Y → Z → Prop
  previous_eligible : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
    eligible x.2.1 x.1 y.1 z.1
  value : Prefix → Tensor ℂ (X × (New × NX)) (Y × (New × NY)) (Z × (New × NZ))
  vanishes : ∀ prior x y z, eligible prior x.1 y.1 z.1 → ∀ j < order,
    (kernel auxiliary (leftMap prior) (middleMap prior) (rightMap prior) x y z).coeff j = 0
  leading : ∀ prior x y z, eligible prior x.1 y.1 z.1 →
    (kernel auxiliary (leftMap prior) (middleMap prior) (rightMap prior) x y z).coeff order =
      value prior x y z
  synchronized : ∀ prior x y z, eligible prior x.1 y.1 z.1 → value prior x y z ≠ 0 →
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1

def pack {OldCoord NewCoord : Type*} :
    ((Prefix × New) × (OldCoord × NewCoord)) → Output Prefix New OldCoord NewCoord :=
  fun output => ((output.1.1, output.2.1), (output.1.2, output.2.2))

namespace Execution

variable (S : Stage E New NX NY NZ BX BY BZ)

def step : Execution X Y Z (Prefix × New) (PX × NX) (PY × NY) (PZ × NZ)
    (AX × BX) (AY × BY) (AZ × BZ) support := by
  have coefficients := controlledKernel_coefficients E.order S.order
    E.auxiliary S.auxiliary E.leftMap E.middleMap E.rightMap
    S.leftMap S.middleMap S.rightMap E.value S.value support S.eligible
    E.vanishes E.leading
    (fun x y z hs hn => ⟨(E.synchronized x y z hs hn).1,
      (E.synchronized x y z hs hn).2, S.previous_eligible x y z hs hn⟩)
    S.vanishes S.leading
  refine {
    auxiliary := Tensor.product E.auxiliary S.auxiliary
    rankBound := E.rankBound * S.rankBound
    auxiliary_rank := E.auxiliary_rank.product S.auxiliary_rank
    order := E.order * (S.order + 1) + S.order
    leftDegree := E.leftDegree * (S.order + 1) + S.leftDegree
    middleDegree := E.middleDegree * (S.order + 1) + S.middleDegree
    rightDegree := E.rightDegree * (S.order + 1) + S.rightDegree
    leftMap := fun x output input =>
      controlledMap S.order E.leftMap S.leftMap x (pack output) input
    middleMap := fun y output input =>
      controlledMap S.order E.middleMap S.middleMap y (pack output) input
    rightMap := fun z output input =>
      controlledMap S.order E.rightMap S.rightMap z (pack output) input
    left_degree := fun x output input =>
      controlledMap_degree S.order E.leftDegree S.leftDegree E.leftMap S.leftMap
        E.left_degree S.left_degree x (pack output) input
    middle_degree := fun y output input =>
      controlledMap_degree S.order E.middleDegree S.middleDegree E.middleMap S.middleMap
        E.middle_degree S.middle_degree y (pack output) input
    right_degree := fun z output input =>
      controlledMap_degree S.order E.rightDegree S.rightDegree E.rightMap S.rightMap
        E.right_degree S.right_degree z (pack output) input
    value := fun x y z => controlledLeading E.value S.value
      (x.1, pack x.2) (y.1, pack y.2) (z.1, pack z.2)
    vanishes := fun x y z hs j hj =>
      coefficients.1 (x.1, pack x.2) (y.1, pack y.2) (z.1, pack z.2) hs j hj
    leading := fun x y z hs =>
      coefficients.2 (x.1, pack x.2) (y.1, pack y.2) (z.1, pack z.2) hs
    synchronized := ?_
  }
  intro x y z hs hn
  have hproduct :
      E.value (x.1, (x.2.1.1, x.2.2.1)) (y.1, (y.2.1.1, y.2.2.1))
        (z.1, (z.2.1.1, z.2.2.1)) *
      S.value x.2.1.1 (x.1, (x.2.1.2, x.2.2.2))
        (y.1, (y.2.1.2, y.2.2.2)) (z.1, (z.2.1.2, z.2.2.2)) ≠ 0 := hn
  have hp := (mul_ne_zero_iff.mp hproduct).1
  have hs' := (mul_ne_zero_iff.mp hproduct).2
  have hprior := E.synchronized _ _ _ hs hp
  have heligible := S.previous_eligible _ _ _ hs hp
  have hnew := S.synchronized _ _ _ _ heligible hs'
  exact ⟨Prod.ext hprior.1 hnew.1, Prod.ext hprior.2 hnew.2⟩

@[simp] theorem step_rankBound : (step E S).rankBound = E.rankBound * S.rankBound := rfl

@[simp] theorem step_auxiliary :
    (step E S).auxiliary = Tensor.product E.auxiliary S.auxiliary := rfl

@[simp] theorem step_order : (step E S).order = E.order * (S.order + 1) + S.order := rfl

@[simp] theorem step_value
    (x : X × ((Prefix × New) × (PX × NX)))
    (y : Y × ((Prefix × New) × (PY × NY)))
    (z : Z × ((Prefix × New) × (PZ × NZ))) :
    (step E S).value x y z =
      E.value (x.1, (x.2.1.1, x.2.2.1)) (y.1, (y.2.1.1, y.2.2.1))
        (z.1, (z.2.1.1, z.2.2.1)) *
      S.value x.2.1.1 (x.1, (x.2.1.2, x.2.2.2))
        (y.1, (y.2.1.2, y.2.2.2)) (z.1, (z.2.1.2, z.2.2.2)) := rfl

end Execution
end MatrixMultiplication.Foundation.PolynomialKernelExecution

end

end OAI
