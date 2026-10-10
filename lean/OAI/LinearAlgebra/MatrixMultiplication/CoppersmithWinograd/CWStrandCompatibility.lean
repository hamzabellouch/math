import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStrands

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWStrandCompatibility

open MatrixMultiplication.Foundation CWStrands CWCompatibilityTransfer InheritedMasks
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem shape_nonzero_power {n : ℕ} (g : Fin 3 → ℕ)
    (x y z : Fin n → Fin 7) (h : shapeTensor (F := F) (Fin n) g x y z ≠ 0) :
    Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0 := by
  have hm := shapeTensor_support g x y z h
  simpa only [shapeTensor, ite_eq_left hm, strand, Tensor.power] using h

section Classes

variable {P A : Type*} [Fintype P] [DecidableEq P]
    [Fintype A] [DecidableEq A] {n : ℕ}
    (g : P → Fin 3 → ℕ) (x y z : P → (Fin n → Fin 7))
    (h : (∏ i, shapeTensor (F := F) (Fin n) (g i) (x i) (y i) (z i)) ≠ 0)
    (statistic : (Fin n → Fin 7) → A) (κ : A ≃ A)
    (hstatistic : ∀ w, statistic (wordComplement w) = κ (statistic w))
    (ν : A → ℝ) (η : ℝ)

include h

omit [DecidableEq P] in
theorem class_coefficient_nonzero (i : P) :
    shapeTensor (F := F) (Fin n) (g i) (x i) (y i) (z i) ≠ 0 := by
  intro hi
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) hi)

include hstatistic

theorem zeroZ_transfer (hg : ∀ i, g i 2 = 0)
    (hx : typeWindow ν η (fun i => statistic (x i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (y i)) := by
  apply transfer_window statistic κ hstatistic x y _ ν η hx
  intro i
  have hi := class_coefficient_nonzero g x y z h i
  have hm := shapeTensor_support (g i) (x i) (y i) (z i) hi
  have hz : wordWeight (z i) = 0 := by
    change weight (z i) = 0
    exact hm.2.2.trans (hg i)
  exact zeroZ_word_match (x i) (y i) (z i)
    (shape_nonzero_power (g i) (x i) (y i) (z i) hi) hz

theorem zeroY_transfer (hg : ∀ i, g i 1 = 0)
    (hx : typeWindow ν η (fun i => statistic (x i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (z i)) := by
  apply transfer_window statistic κ hstatistic x z _ ν η hx
  intro i
  have hi := class_coefficient_nonzero g x y z h i
  have hm := shapeTensor_support (g i) (x i) (y i) (z i) hi
  have hy : wordWeight (y i) = 0 := by
    change weight (y i) = 0
    exact hm.2.1.trans (hg i)
  exact zeroY_word_match (x i) (y i) (z i)
    (shape_nonzero_power (g i) (x i) (y i) (z i) hi) hy

theorem zeroX_transfer (hg : ∀ i, g i 0 = 0)
    (hy : typeWindow ν η (fun i => statistic (y i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (z i)) := by
  apply transfer_window statistic κ hstatistic y z _ ν η hy
  intro i
  have hi := class_coefficient_nonzero g x y z h i
  have hm := shapeTensor_support (g i) (x i) (y i) (z i) hi
  have hx : wordWeight (x i) = 0 := by
    change weight (x i) = 0
    exact hm.1.trans (hg i)
  exact zeroX_word_match (x i) (y i) (z i)
    (shape_nonzero_power (g i) (x i) (y i) (z i) hi) hx

end Classes

end MatrixMultiplication.CWStrandCompatibility

end

end OAI
