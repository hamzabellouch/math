import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWWindowedLeaves
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FiniteFamily

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section
namespace MatrixMultiplication.CWOrientedZero
open MatrixMultiplication.Foundation CWWindowedLeaves CWStrands AllFieldFiniteFamily
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (F : Type*) [Field F]

private theorem tensor_swapXY (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 y x z := by
  unfold FieldCW.tensor
  simp only [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  ring

private theorem tensor_swapYZ (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 x z y := by
  exact (FieldCW.tensor_cyclic F 5 x y z).trans
    ((tensor_swapXY F y z x).trans (FieldCW.tensor_cyclic F 5 x z y).symm)

private theorem tensor_swapXZ (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 z y x := by
  exact (FieldCW.tensor_cyclic F 5 x y z).trans (tensor_swapXY F y z x)

private theorem shape_swapXY (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) ![a,b,c] x y z =
      shapeTensor (F := F) (Fin n) ![b,a,c] y x z := by
  have hp : strand (F := F) (Fin n) x y z = strand (F := F) (Fin n) y x z := by
    apply Finset.prod_congr rfl
    intro i _
    exact tensor_swapXY F _ _ _
  simp only [shapeTensor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hp]
  congr 1
  apply propext
  tauto

private theorem shape_swapYZ (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) ![a,b,c] x y z =
      shapeTensor (F := F) (Fin n) ![a,c,b] x z y := by
  have hp : strand (F := F) (Fin n) x y z = strand (F := F) (Fin n) x z y := by
    apply Finset.prod_congr rfl
    intro i _
    exact tensor_swapYZ F _ _ _
  simp only [shapeTensor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hp]
  congr 1
  apply propext
  tauto

private theorem shape_swapXZ (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) ![a,b,c] x y z =
      shapeTensor (F := F) (Fin n) ![c,b,a] z y x := by
  rw [shape_swapXY, shape_swapYZ, shape_swapXY]

def placedShape (zero selected : Fin 3) (a b : ℕ) : Fin 3 → ℕ :=
  fun s => if s = zero then 0 else if s = selected then a else b

def sideWord (zero selected : Fin 3) {n a : ℕ} (side : Fin 3)
    (w : Alphabet n a) : Raw n :=
  if side = zero then zeroWord n else if side = selected then w.val else complementWord w.val

def matched (zero : Fin 3) {E : Type*} (x y z : E) : Prop :=
  if zero = 0 then y = z else if zero = 1 then x = z else x = y

theorem local_coefficient (n a b : ℕ) (hab : a + b = 2*n)
    (zero selected : Fin 3) (hne : zero ≠ selected) (x y z : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (placedShape zero selected a b)
      (sideWord zero selected 0 x) (sideWord zero selected 1 y)
      (sideWord zero selected 2 z) = if matched zero x y z then 1 else 0 := by
  fin_cases zero <;> fin_cases selected
  all_goals try contradiction
  · simp [shapeTensor, placedShape, sideWord, matched]
    exact zeroX_local F n a b hab y z
  · have hh := (shape_swapYZ F n 0 b a (zeroWord n) (complementWord y.val) z.val).trans
        (zeroX_local F n a b hab z y)
    have he : (z = y) ↔ (y = z) := eq_comm
    simp only [he] at hh
    simp [shapeTensor, placedShape, sideWord, matched]
    exact hh
  · simp [shapeTensor, placedShape, sideWord, matched]
    exact zeroY_local F n a b hab x z
  · have hh := (shape_swapXZ F n b 0 a (complementWord x.val) (zeroWord n) z.val).trans
        (zeroY_local F n a b hab z x)
    have he : (z = x) ↔ (x = z) := eq_comm
    simp only [he] at hh
    simp [shapeTensor, placedShape, sideWord, matched]
    exact hh
  · simp [shapeTensor, placedShape, sideWord, matched]
    exact zeroZ_local F n a b hab x y
  · have hh := (shape_swapXY F n b a 0 (complementWord x.val) y.val (zeroWord n)).trans
        (zeroZ_local F n a b hab y x)
    have he : (y = x) ↔ (x = y) := eq_comm
    simp only [he] at hh
    simp [shapeTensor, placedShape, sideWord, matched]
    exact hh

def Row (zero : Fin 3) (E : Type) : Type := if zero = 1 then E else Unit
def Middle (zero : Fin 3) (E : Type) : Type := if zero = 2 then E else Unit
def Column (zero : Fin 3) (E : Type) : Type := if zero = 0 then E else Unit
instance (zero : Fin 3) (E : Type) [Fintype E] : Fintype (Row zero E) := by
  unfold Row; split_ifs <;> infer_instance
instance (zero : Fin 3) (E : Type) [Fintype E] : Fintype (Middle zero E) := by
  unfold Middle; split_ifs <;> infer_instance
instance (zero : Fin 3) (E : Type) [Fintype E] : Fintype (Column zero E) := by
  unfold Column; split_ifs <;> infer_instance

theorem volume (zero : Fin 3) (E : Type) [Fintype E] :
    Fintype.card (Row zero E) * Fintype.card (Middle zero E) *
      Fintype.card (Column zero E) = Fintype.card E := by
  have hunit (inst : Fintype Unit) : @Fintype.card Unit inst = 1 :=
    @Fintype.card_unique Unit (uniqueOfSubsingleton ()) inst
  fin_cases zero
  · have hr := Fintype.card_congr' (show Row (0 : Fin 3) E = Unit by simp [Row])
    have hm := Fintype.card_congr' (show Middle (0 : Fin 3) E = Unit by simp [Middle])
    have hc := Fintype.card_congr' (show Column (0 : Fin 3) E = E by simp [Column])
    exact (congrArg₂ Nat.mul
      (congrArg₂ Nat.mul (hr.trans (hunit _)) (hm.trans (hunit _))) hc).trans
      (Nat.one_mul (Fintype.card E))
  · have hr := Fintype.card_congr' (show Row (1 : Fin 3) E = E by simp [Row])
    have hm := Fintype.card_congr' (show Middle (1 : Fin 3) E = Unit by simp [Middle])
    have hc := Fintype.card_congr' (show Column (1 : Fin 3) E = Unit by simp [Column])
    exact (congrArg₂ Nat.mul
      (congrArg₂ Nat.mul hr (hm.trans (hunit _))) (hc.trans (hunit _))).trans
      ((Nat.mul_one (Nat.mul (Fintype.card E) 1)).trans (Nat.mul_one (Fintype.card E)))
  · have hr := Fintype.card_congr' (show Row (2 : Fin 3) E = Unit by simp [Row])
    have hm := Fintype.card_congr' (show Middle (2 : Fin 3) E = E by simp [Middle])
    have hc := Fintype.card_congr' (show Column (2 : Fin 3) E = Unit by simp [Column])
    exact (congrArg₂ Nat.mul
      (congrArg₂ Nat.mul (hr.trans (hunit _)) hm) (hc.trans (hunit _))).trans
      ((Nat.mul_one (Nat.mul 1 (Fintype.card E))).trans (Nat.one_mul (Fintype.card E)))

theorem matching_nonempty {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    (Q : Tensor F V V V) (zero : Fin 3) (embed : Fin 3 → E → V)
    (h : ∀ x y z, Q (embed 0 x) (embed 1 y) (embed 2 z) =
      if matched zero x y z then 1 else 0) :
    Nonempty (LocalMap Q (Tensor.matrixCoefficients (Row zero E) (Middle zero E) (Column zero E))) := by
  let e : E := Classical.choice inferInstance
  fin_cases zero
  · refine ⟨LocalMap.ofExists ⟨(fun _ v => if v = embed 0 e then 1 else 0),
      (fun y v => if v = embed 1 y.2 then 1 else 0),
      (fun z v => if v = embed 2 z.1 then 1 else 0), ?_⟩⟩
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    let sm0 : Subsingleton (Middle (0 : Fin 3) E) := by simp only [Middle, show (0 : Fin 3) ≠ 2 from by decide, ite_false]; infer_instance
    let sr0 : Subsingleton (Row (0 : Fin 3) E) := by simp only [Row, show (0 : Fin 3) ≠ 1 from by decide, ite_false]; infer_instance
    have hu1 : x.2 = y.1 := @Subsingleton.elim _ sm0 _ _
    have hu2 : z.2 = x.1 := @Subsingleton.elim _ sr0 _ _
    simpa [Tensor.pullback, Tensor.matrixCoefficients, matched, Row, Middle, Column, hu1, hu2] using
      h e y.2 z.1
  · refine ⟨LocalMap.ofExists ⟨(fun x v => if v = embed 0 x.1 then 1 else 0),
      (fun _ v => if v = embed 1 e then 1 else 0),
      (fun z v => if v = embed 2 z.2 then 1 else 0), ?_⟩⟩
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    let sm1 : Subsingleton (Middle (1 : Fin 3) E) := by simp only [Middle, show (1 : Fin 3) ≠ 2 from by decide, ite_false]; infer_instance
    let sc1 : Subsingleton (Column (1 : Fin 3) E) := by simp only [Column, show (1 : Fin 3) ≠ 0 from by decide, ite_false]; infer_instance
    have hu1 : x.2 = y.1 := @Subsingleton.elim _ sm1 _ _
    have hu2 : y.2 = z.1 := @Subsingleton.elim _ sc1 _ _
    simpa [Tensor.pullback, Tensor.matrixCoefficients, matched, Row, Middle, Column,
      hu1, hu2, eq_comm] using
      h x.1 e z.2
  · refine ⟨LocalMap.ofExists ⟨(fun x v => if v = embed 0 x.2 then 1 else 0),
      (fun y v => if v = embed 1 y.1 then 1 else 0),
      (fun _ v => if v = embed 2 e then 1 else 0), ?_⟩⟩
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    let sc2 : Subsingleton (Column (2 : Fin 3) E) := by simp only [Column, show (2 : Fin 3) ≠ 0 from by decide, ite_false]; infer_instance
    let sr2 : Subsingleton (Row (2 : Fin 3) E) := by simp only [Row, show (2 : Fin 3) ≠ 1 from by decide, ite_false]; infer_instance
    have hu1 : y.2 = z.1 := @Subsingleton.elim _ sc2 _ _
    have hu2 : z.2 = x.1 := @Subsingleton.elim _ sr2 _ _
    simpa [Tensor.pullback, Tensor.matrixCoefficients, matched, Row, Middle, Column, hu1, hu2] using
      h x.2 y.1 e

def ofMatching {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    (Q : Tensor F V V V) (zero : Fin 3) (embed : Fin 3 → E → V)
    (h : ∀ x y z, Q (embed 0 x) (embed 1 y) (embed 2 z) =
      if matched zero x y z then 1 else 0) :
    LocalMap Q (Tensor.matrixCoefficients (Row zero E) (Middle zero E) (Column zero E)) :=
  Classical.choice (matching_nonempty F Q zero embed h)

theorem power_coefficient {E : Type} (n a b m : ℕ) (hab : a+b=2*n)
    (zero selected : Fin 3) (hne : zero ≠ selected)
    (words : E → Fin m → Alphabet n a) (hinj : Function.Injective words)
    (x y z : E) :
    Tensor.power (shapeTensor (F := F) (Fin n) (placedShape zero selected a b)) m
      (fun i => sideWord zero selected 0 (words x i))
      (fun i => sideWord zero selected 1 (words y i))
      (fun i => sideWord zero selected 2 (words z i)) =
      if matched zero x y z then 1 else 0 := by
  simp only [Tensor.power, local_coefficient F n a b hab zero selected hne]
  fin_cases zero <;> simp [matched, Fintype.prod_boole, ← funext_iff, hinj.eq_iff]

end MatrixMultiplication.CWOrientedZero

end

end OAI
