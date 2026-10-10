import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.InitialState

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.CWOrientedZero
open MatrixMultiplication.Foundation CWWindowedLeaves CWStrands AllFieldFiniteFamily
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (F : Type*) [Field F]

private theorem tensor_swapXY_inline_MatrixMultiplication_CWOrientedZero (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 y x z := by
  unfold FieldCW.tensor
  simp only [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  ring

private theorem tensor_swapYZ_inline_MatrixMultiplication_CWOrientedZero (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 x z y := by
  exact (FieldCW.tensor_cyclic F 5 x y z).trans
    ((tensor_swapXY_inline_MatrixMultiplication_CWOrientedZero F y z x).trans (FieldCW.tensor_cyclic F 5 x z y).symm)

private theorem tensor_swapXZ_inline_MatrixMultiplication_CWOrientedZero (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 z y x := by
  exact (FieldCW.tensor_cyclic F 5 x y z).trans (tensor_swapXY_inline_MatrixMultiplication_CWOrientedZero F y z x)

private theorem shape_swapXY (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (c) Matrix.vecEmpty))) x y z =
      shapeTensor (F := F) (Fin n) (Matrix.vecCons (b) (Matrix.vecCons (a) (Matrix.vecCons (c) Matrix.vecEmpty))) y x z := by
  have hp : strand (F := F) (Fin n) x y z = strand (F := F) (Fin n) y x z := by
    apply Finset.prod_congr rfl
    intro i _
    exact tensor_swapXY_inline_MatrixMultiplication_CWOrientedZero F _ _ _
  simp only [shapeTensor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hp]
  congr 1
  apply propext
  tauto

private theorem shape_swapYZ (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (c) Matrix.vecEmpty))) x y z =
      shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (c) (Matrix.vecCons (b) Matrix.vecEmpty))) x z y := by
  have hp : strand (F := F) (Fin n) x y z = strand (F := F) (Fin n) x z y := by
    apply Finset.prod_congr rfl
    intro i _
    exact tensor_swapYZ_inline_MatrixMultiplication_CWOrientedZero F _ _ _
  simp only [shapeTensor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hp]
  congr 1
  apply propext
  tauto

private theorem shape_swapXZ (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (c) Matrix.vecEmpty))) x y z =
      shapeTensor (F := F) (Fin n) (Matrix.vecCons (c) (Matrix.vecCons (b) (Matrix.vecCons (a) Matrix.vecEmpty))) z y x := by
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
  have shape_eq : placedShape zero selected a b =
      ![placedShape zero selected a b 0, placedShape zero selected a b 1,
        placedShape zero selected a b 2] := by
    ext side
    fin_cases side <;> rfl
  rw [shape_eq]
  fin_cases zero <;> fin_cases selected
  all_goals try contradiction
  · simpa [placedShape, sideWord, matched] using zeroX_local F n a b hab y z
  · have hh := (shape_swapYZ F n 0 b a (zeroWord n) (complementWord y.val) z.val).trans
        (zeroX_local F n a b hab z y)
    have he : (z = y) ↔ (y = z) := eq_comm
    simpa [placedShape, sideWord, matched, he] using hh
  · simpa [placedShape, sideWord, matched] using zeroY_local F n a b hab x z
  · have hh := (shape_swapXZ F n b 0 a (complementWord x.val) (zeroWord n) z.val).trans
        (zeroY_local F n a b hab z x)
    have he : (z = x) ↔ (x = z) := eq_comm
    simpa [placedShape, sideWord, matched, he] using hh
  · simpa [placedShape, sideWord, matched] using zeroZ_local F n a b hab x y
  · have hh := (shape_swapXY F n b a 0 (complementWord x.val) y.val (zeroWord n)).trans
        (zeroZ_local F n a b hab y x)
    have he : (y = x) ↔ (x = y) := eq_comm
    simpa [placedShape, sideWord, matched, he] using hh

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
  fin_cases zero
  · change Fintype.card Unit * Fintype.card Unit * Fintype.card E = Fintype.card E
    simp
  · change Fintype.card E * Fintype.card Unit * Fintype.card Unit = Fintype.card E
    simp
  · change Fintype.card Unit * Fintype.card E * Fintype.card Unit = Fintype.card E
    simp

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
    simpa [Tensor.pullback, Tensor.matrixCoefficients, matched, Row, Middle, Column, hu1, hu2, eq_comm] using
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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.CWZeroGeometry

open AllFieldParameters AllFieldHistory CWOrientedZero

def zeroAxis (g : Shape) : Fin 3 :=
  if g 0 = 0 then 0 else if g 1 = 0 then 1 else 2

def maxAxis (g : Shape) : Fin 3 :=
  if g 0 = shapeMax g then 0 else if g 1 = shapeMax g then 1 else 2

theorem zeroAxis_spec (g : Shape) (hz : ∃ i, g i = 0) : g (zeroAxis g) = 0 := by
  unfold zeroAxis
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · obtain ⟨i, hi⟩ := hz
    fin_cases i <;> simp_all

theorem maxAxis_spec (g : Shape) : g (maxAxis g) = shapeMax g := by
  have hm : shapeMax g = g 0 ∨ shapeMax g = g 1 ∨ shapeMax g = g 2 := by
    unfold shapeMax
    rcases le_total (g 0) (max (g 1) (g 2)) with h | h
    · rw [max_eq_right h]
      rcases le_total (g 1) (g 2) with h | h
      · exact Or.inr (Or.inr (max_eq_right h))
      · exact Or.inr (Or.inl (max_eq_left h))
    · exact Or.inl (max_eq_left h)
  unfold maxAxis
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · rcases hm with hm | hm | hm
    · exact (h0 hm.symm).elim
    · exact (h1 hm.symm).elim
    · exact hm.symm

theorem shapeMax_le_total (g : Shape) : shapeMax g ≤ shapeTotal g := by
  exact max_le (coordinate_le_total g 0)
    (max_le (coordinate_le_total g 1) (coordinate_le_total g 2))

theorem shapeMax_pos (g : Shape) (ht : 0 < shapeTotal g) : 0 < shapeMax g := by
  have h0 : g 0 ≤ shapeMax g := le_max_left _ _
  have h1 : g 1 ≤ shapeMax g := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : g 2 ≤ shapeMax g := (le_max_right _ _).trans (le_max_right _ _)
  unfold shapeTotal at ht
  omega

theorem zero_ne_selected (g : Shape) (zero selected : Fin 3)
    (ht : 0 < shapeTotal g) (hz : g zero = 0) (hs : g selected = shapeMax g) :
    zero ≠ selected := by
  intro he
  have hp := shapeMax_pos g ht
  rw [← he, hz] at hs
  omega

theorem max_add_complement (g : Shape) :
    shapeMax g + (shapeTotal g - shapeMax g) = shapeTotal g :=
  Nat.add_sub_of_le (shapeMax_le_total g)

theorem eq_placedShape (g : Shape) (zero selected : Fin 3)
    (hz : g zero = 0) (hs : g selected = shapeMax g) (hne : zero ≠ selected) :
    g = placedShape zero selected (shapeMax g) (shapeTotal g - shapeMax g) := by
  funext side
  fin_cases zero <;> fin_cases selected
  all_goals try contradiction
  all_goals fin_cases side <;>
    simp_all [placedShape, shapeTotal]

theorem physicalShape_eq_placedShape (g : Shape) (phi : Equiv.Perm (Fin 3))
    (zero selected : Fin 3) (hz : g zero = 0)
    (hs : g selected = shapeMax g) (hne : zero ≠ selected) :
    physicalShape phi g = placedShape (phi zero) (phi selected)
      (shapeMax g) (shapeTotal g - shapeMax g) := by
  funext side
  calc
    physicalShape phi g side =
        placedShape zero selected (shapeMax g) (shapeTotal g - shapeMax g)
          (phi.symm side) := congrFun (eq_placedShape g zero selected hz hs hne) _
    _ = _ := by simp only [placedShape, Equiv.symm_apply_eq]

theorem selected_add_remaining (g : Shape) (zero selected side : Fin 3)
    (hz : g zero = 0) (hs : g selected = shapeMax g) (hne : zero ≠ selected)
    (hzs : side ≠ zero) (hss : side ≠ selected) :
    g selected + g side = shapeTotal g := by
  have hside : g side = shapeTotal g - shapeMax g := by
    rw [congrFun (eq_placedShape g zero selected hz hs hne) side]
    simp only [placedShape, ite_eq_right hzs, ite_eq_right hss]
  rw [hs, hside]
  exact max_add_complement g

end MatrixMultiplication.CWZeroGeometry

end

end MatrixAllFields

end OAI
