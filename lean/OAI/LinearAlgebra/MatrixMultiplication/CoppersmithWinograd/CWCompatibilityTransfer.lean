import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWLeafStatistics
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMasks

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWCompatibilityTransfer

open MatrixMultiplication.Foundation CWLeafRestrictions InheritedMasks
open scoped BigOperators

def wordWeight {n : ℕ} (w : Fin n → Fin 7) : ℕ := ∑ i, CWLeafStatistics.weight (w i)

def wordComplement {n : ℕ} (w : Fin n → Fin 7) : Fin n → Fin 7 :=
  fun i => complement 5 (w i)

@[simp] theorem wordComplement_involution {n : ℕ} (w : Fin n → Fin 7) :
    wordComplement (wordComplement w) = w := by
  funext i
  exact complement_involution 5 (w i)

theorem weight_eq_zero_iff : ∀ x : Fin 7, CWLeafStatistics.weight x = 0 ↔ x = 0 := by
  decide +kernel

theorem wordWeight_zero {n : ℕ} (w : Fin n → Fin 7) (h : wordWeight w = 0) :
    ∀ i, w i = 0 := by
  intro i
  have hle : CWLeafStatistics.weight (w i) ≤ wordWeight w := by
    unfold wordWeight
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (CWLeafStatistics.weight (w j)))
      (Finset.mem_univ i)
  apply (weight_eq_zero_iff (w i)).mp
  omega

theorem site_nonzero {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0) (i : Fin n) :
    FieldCW.tensor F 5 (x i) (y i) (z i) ≠ 0 := by
  intro hi
  apply h
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem zeroX_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hx : wordWeight x = 0) : z = wordComplement y := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero x hx i] at hi
  have heq : FieldCW.tensor F 5 0 (y i) (z i) =
      if y i = complement 5 (z i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_zero_matching F 5 (y i) (complement 5 (z i))
  have hyz : y i = complement 5 (z i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hyz
  simpa only [wordComplement, complement_involution] using hh.symm

theorem zeroY_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hy : wordWeight y = 0) : z = wordComplement x := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero y hy i] at hi
  have heq : FieldCW.tensor F 5 (x i) 0 (z i) =
      if x i = complement 5 (z i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_middle_zero_matching F 5 (x i) (complement 5 (z i))
  have hxz : x i = complement 5 (z i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hxz
  simpa only [wordComplement, complement_involution] using hh.symm

theorem zeroZ_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hz : wordWeight z = 0) : y = wordComplement x := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero z hz i] at hi
  have heq : FieldCW.tensor F 5 (x i) (y i) 0 =
      if x i = complement 5 (y i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_last_zero_matching F 5 (x i) (complement 5 (y i))
  have hxy : x i = complement 5 (y i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hxy
  simpa only [wordComplement, complement_involution] using hh.symm

theorem transfer_window {P A : Type*} [Fintype P] [DecidableEq P]
    [Fintype A] [DecidableEq A] {n : ℕ}
    (statistic : (Fin n → Fin 7) → A) (κ : A ≃ A)
    (hstatistic : ∀ w, statistic (wordComplement w) = κ (statistic w))
    (x y : P → (Fin n → Fin 7)) (hmatch : ∀ i, y i = wordComplement (x i))
    (ν : A → ℝ) (η : ℝ)
    (hx : typeWindow ν η (fun i => statistic (x i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (y i)) := by
  have heq : (fun i => statistic (y i)) = κ ∘ (fun i => statistic (x i)) := by
    funext i
    rw [hmatch i, hstatistic]
    rfl
  rw [heq]
  exact (typeWindow_equiv ν η (fun i => statistic (x i)) κ).mpr hx

end MatrixMultiplication.CWCompatibilityTransfer

end

end OAI
