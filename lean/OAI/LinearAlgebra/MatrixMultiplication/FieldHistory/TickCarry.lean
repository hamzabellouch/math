import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Regrouping

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

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

end OAI
