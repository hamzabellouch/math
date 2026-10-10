import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.FieldCW
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.LeafVolumes

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

namespace MatrixMultiplication.CWLeafRestrictions

open MatrixMultiplication.Foundation

def lastLabel (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

def complement (q : ℕ) : Fin (q + 2) ≃ Fin (q + 2) :=
  Equiv.swap 0 (lastLabel q)

@[simp] theorem complement_zero (q : ℕ) : complement q 0 = lastLabel q := by
  simp [complement]

@[simp] theorem complement_last (q : ℕ) : complement q (lastLabel q) = 0 := by
  simp [complement]

@[simp] theorem complement_involution (q : ℕ) (x : Fin (q + 2)) :
    complement q (complement q x) = x := by
  simp [complement]

theorem complement_interior (q : ℕ) (x : Fin (q + 2))
    (hx0 : x.val ≠ 0) (hxlast : x.val ≠ q + 1) : complement q x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hx0 (congrArg Fin.val h)
  · intro h
    exact hxlast (congrArg Fin.val h)

theorem zero_support_iff (q : ℕ) (y z : Fin (q + 2)) :
    ((y.val = 0 ∧ z.val = q + 1) ∨
      (y.val = q + 1 ∧ z.val = 0) ∨
      (1 ≤ y.val ∧ y.val ≤ q ∧ y = z)) ↔ complement q y = z := by
  by_cases hy0 : y.val = 0
  · have hy : y = 0 := Fin.ext hy0
    subst y
    rw [complement_zero]
    constructor
    · rintro (⟨_, hz⟩ | ⟨hy, _⟩ | ⟨hy, _⟩)
      · exact Fin.ext hz.symm
      · have : (0 : ℕ) = q + 1 := hy
        omega
      · have : 1 ≤ (0 : ℕ) := hy
        omega
    · intro h
      exact Or.inl ⟨rfl, (congrArg Fin.val h).symm⟩
  · by_cases hylast : y.val = q + 1
    · have hy : y = lastLabel q := Fin.ext hylast
      subst y
      rw [complement_last]
      constructor
      · rintro (⟨hy, _⟩ | ⟨_, hz⟩ | ⟨_, hy, _⟩)
        · have : q + 1 = 0 := hy
          omega
        · exact Fin.ext hz.symm
        · have : q + 1 ≤ q := hy
          omega
      · intro h
        exact Or.inr (Or.inl ⟨rfl, (congrArg Fin.val h).symm⟩)
    · have hlo : 1 ≤ y.val := by omega
      have hhi : y.val ≤ q := by have := y.isLt; omega
      rw [complement_interior q y hy0 hylast]
      simp [hy0, hylast, hlo, hhi]

theorem tensor_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (y z : Fin (q + 2)) :
    FieldCW.tensor F q 0 y (complement q z) = if y = z then 1 else 0 := by
  rw [FieldCW.tensor_zero_side F q 0 y (complement q z) rfl]
  simp only [zero_support_iff, Equiv.apply_eq_iff_eq]

theorem tensor_middle_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (x z : Fin (q + 2)) :
    FieldCW.tensor F q x 0 (complement q z) = if x = z then 1 else 0 := by
  rw [FieldCW.tensor_cyclic F q x 0 (complement q z)]
  have h := tensor_zero_matching F q (complement q z) (complement q x)
  simpa only [complement_involution, Equiv.apply_eq_iff_eq, eq_comm] using h

theorem tensor_last_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (x y : Fin (q + 2)) :
    FieldCW.tensor F q x (complement q y) 0 = if x = y then 1 else 0 := by
  rw [FieldCW.tensor_cyclic F q x (complement q y) 0,
    FieldCW.tensor_cyclic F q (complement q y) 0 x]
  exact tensor_zero_matching F q x y

theorem zeroX_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => complement q (z.1.val i))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients Unit Unit {w // p w} :=
  LeafVolumes.matchingPower_matrixCoefficients (FieldCW.tensor F q) 0
    (complement q) (tensor_zero_matching F q) n p

theorem zeroY_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun x : {w // p w} × Unit => x.1.val)
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (fun z : Unit × {w // p w} => fun i => complement q (z.2.val i))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, tensor_middle_zero_matching,
    Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff, eq_comm]

theorem zeroZ_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun x : Unit × {w // p w} => x.2.val)
      (fun y : {w // p w} × Unit => fun i => complement q (y.1.val i))
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, tensor_last_zero_matching,
    Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff]

end MatrixMultiplication.CWLeafRestrictions

end OAI
