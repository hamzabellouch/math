import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWOrientedZero
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ShapeEncoding

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

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

end OAI
