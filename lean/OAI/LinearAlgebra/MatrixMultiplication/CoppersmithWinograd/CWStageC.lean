import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStrands

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWStageC

open MatrixMultiplication.Foundation CWStrands CWLeafRestrictions

def interior (i : Fin 5) : Fin 7 := ⟨i.val + 1, by have := i.isLt; omega⟩

theorem interior_injective : Function.Injective interior := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa only [interior, Nat.add_right_cancel_iff] using hval

@[simp] theorem interior_weight (i : Fin 5) : CWLeafStatistics.weight (interior i) = 1 := by
  have hi : i.val + 1 ≠ 6 := by have := i.isLt; omega
  simp [CWLeafStatistics.weight, interior, hi]

@[simp] theorem zero_weight : CWLeafStatistics.weight (0 : Fin 7) = 0 := rfl

@[simp] theorem last_weight : CWLeafStatistics.weight (6 : Fin 7) = 2 := rfl

@[simp] theorem interior_complement (i : Fin 5) : complement 5 (interior i) = interior i := by
  apply complement_interior
  · simp [interior]
  · dsimp [interior]
    have := i.isLt
    omega

variable (F : Type*) [CommRing F]

theorem coefficient110 (i j : Fin 5) :
    FieldCW.tensor F 5 (interior i) (interior j) 0 = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_last_zero_matching F 5 (interior i) (interior j)

theorem coefficient101 (i j : Fin 5) :
    FieldCW.tensor F 5 (interior i) 0 (interior j) = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_middle_zero_matching F 5 (interior i) (interior j)

theorem coefficient011 (i j : Fin 5) :
    FieldCW.tensor F 5 0 (interior i) (interior j) = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_zero_matching F 5 (interior i) (interior j)

theorem coefficient002 : FieldCW.tensor F 5 0 0 6 = 1 := by
  simpa [complement, lastLabel] using tensor_zero_matching F 5 0 0

theorem branch0 :
    Tensor.pullback (fun x : Unit × Fin 5 => ![0, interior x.2])
      (fun y : Fin 5 × Unit => ![0, interior y.1])
      (fun _ : Unit × Unit => ![6, 0])
      (shapeTensor (F := F) (Fin 2) ![1, 1, 2]) =
      Tensor.matrixCoefficients Unit (Fin 5) Unit := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient002, coefficient110, Tensor.matrixCoefficients]

theorem branch1 :
    Tensor.pullback (fun x : Unit × Fin 5 => ![interior x.2, 0])
      (fun y : Fin 5 × Unit => ![interior y.1, 0])
      (fun _ : Unit × Unit => ![0, 6])
      (shapeTensor (F := F) (Fin 2) ![1, 1, 2]) =
      Tensor.matrixCoefficients Unit (Fin 5) Unit := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient002, coefficient110, Tensor.matrixCoefficients]

theorem branch2 :
    Tensor.pullback (fun x : Fin 5 × Unit => ![0, interior x.1])
      (fun y : Unit × Fin 5 => ![interior y.2, 0])
      (fun z : Fin 5 × Fin 5 => ![interior z.1, interior z.2])
      (shapeTensor (F := F) (Fin 2) ![1, 1, 2]) =
      Tensor.matrixCoefficients (Fin 5) Unit (Fin 5) := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient011, coefficient101, Tensor.matrixCoefficients]
  all_goals (split_ifs <;> simp_all [eq_comm])

theorem branch3 :
    Tensor.pullback (fun x : Fin 5 × Unit => ![interior x.1, 0])
      (fun y : Unit × Fin 5 => ![0, interior y.2])
      (fun z : Fin 5 × Fin 5 => ![interior z.2, interior z.1])
      (shapeTensor (F := F) (Fin 2) ![1, 1, 2]) =
      Tensor.matrixCoefficients (Fin 5) Unit (Fin 5) := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient011, coefficient101, Tensor.matrixCoefficients]
  all_goals (split_ifs <;> simp_all [eq_comm])

end MatrixMultiplication.CWStageC

end

end OAI
