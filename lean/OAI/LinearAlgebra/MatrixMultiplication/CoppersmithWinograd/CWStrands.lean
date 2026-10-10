import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWCompatibilityTransfer

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWStrands

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {F : Type*} [CommRing F]

private theorem site_weight_zero_support (x y z : Fin 7) (hx : x.val = 0)
    (h : FieldCW.tensor F 5 x y z ≠ 0) :
    CWLeafStatistics.weight x + CWLeafStatistics.weight y + CWLeafStatistics.weight z = 2 := by
  rw [FieldCW.tensor_zero_side F 5 x y z hx] at h
  have hs : (y.val = 0 ∧ z.val = 6) ∨ (y.val = 6 ∧ z.val = 0) ∨
      (1 ≤ y.val ∧ y.val ≤ 5 ∧ y = z) := by
    by_contra hs
    exact h (ite_eq_right hs)
  rcases hs with ⟨hy, hz⟩ | ⟨hy, hz⟩ | ⟨hylo, hyhi, hyz⟩
  · simp [CWLeafStatistics.weight, hx, hy, hz]
  · simp [CWLeafStatistics.weight, hx, hy, hz]
  · subst z
    have hy0 : y.val ≠ 0 := by omega
    have hy6 : y.val ≠ 6 := by omega
    simp [CWLeafStatistics.weight, hx, hy0, hy6]

theorem site_weight_support (x y z : Fin 7)
    (h : FieldCW.tensor F 5 x y z ≠ 0) :
    CWLeafStatistics.weight x + CWLeafStatistics.weight y + CWLeafStatistics.weight z = 2 := by
  by_cases hx : x.val = 0
  · exact site_weight_zero_support x y z hx h
  by_cases hy : y.val = 0
  · rw [FieldCW.tensor_cyclic F 5 x y z] at h
    have hw := site_weight_zero_support y z x hy h
    omega
  by_cases hz : z.val = 0
  · rw [FieldCW.tensor_cyclic F 5 x y z, FieldCW.tensor_cyclic F 5 y z x] at h
    have hw := site_weight_zero_support z x y hz h
    omega
  · exact False.elim (h (by simp [FieldCW.tensor, FieldCW.zeroForm, hx, hy, hz]))

def weight {P : Type*} [Fintype P] (w : P → Fin 7) : ℕ :=
  ∑ i, CWLeafStatistics.weight (w i)

def strand (P : Type*) [Fintype P] : Tensor F (P → Fin 7) (P → Fin 7) (P → Fin 7) :=
  fun x y z => ∏ i, FieldCW.tensor F 5 (x i) (y i) (z i)

theorem strand_support {P : Type*} [Fintype P]
    (x y z : P → Fin 7) (h : strand (F := F) P x y z ≠ 0) :
    weight x + weight y + weight z = 2 * Fintype.card P := by
  have hi (i : P) : FieldCW.tensor F 5 (x i) (y i) (z i) ≠ 0 := by
    intro he
    exact h (Finset.prod_eq_zero (Finset.mem_univ i) he)
  calc
    weight x + weight y + weight z =
        ∑ i, (CWLeafStatistics.weight (x i) + CWLeafStatistics.weight (y i) +
          CWLeafStatistics.weight (z i)) := by simp [weight, Finset.sum_add_distrib]
    _ = ∑ _i : P, 2 := Finset.sum_congr rfl (fun i _ => site_weight_support _ _ _ (hi i))
    _ = 2 * Fintype.card P := by simp [Nat.mul_comm]

def shapeTensor (P : Type*) [Fintype P] (g : Fin 3 → ℕ) :
    Tensor F (P → Fin 7) (P → Fin 7) (P → Fin 7) :=
  fun x y z => if weight x = g 0 ∧ weight y = g 1 ∧ weight z = g 2
    then strand P x y z else 0

theorem shapeTensor_support {P : Type*} [Fintype P]
    (g : Fin 3 → ℕ) (x y z : P → Fin 7)
    (h : shapeTensor (F := F) P g x y z ≠ 0) :
    weight x = g 0 ∧ weight y = g 1 ∧ weight z = g 2 := by
  classical
  by_contra hn
  exact h (ite_eq_right hn)

theorem weight_sum_elim {P Q : Type*} [Fintype P] [Fintype Q]
    (x : P → Fin 7) (y : Q → Fin 7) :
    weight (Sum.elim x y) = weight x + weight y := by
  simp [weight, Fintype.sum_sum_type]

theorem strand_sum_elim {P Q : Type*} [Fintype P] [Fintype Q]
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    strand (F := F) (P ⊕ Q) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) =
      Tensor.product (strand P) (strand Q) x y z := by
  simp [strand, Tensor.product, Fintype.prod_sum_type]

theorem shape_split {P Q : Type*} [Fintype P] [Fintype Q]
    (u v : Fin 3 → ℕ)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    (if weight x.1 = u 0 ∧ weight y.1 = u 1 ∧ weight z.1 = u 2 then
      shapeTensor (F := F) (P ⊕ Q) (u + v) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2)
        (Sum.elim z.1 z.2) else 0) =
      Tensor.product (shapeTensor P u) (shapeTensor Q v) x y z := by
  classical
  simp only [shapeTensor, weight_sum_elim, Pi.add_apply, strand_sum_elim,
    Tensor.product]
  by_cases hx : weight x.1 = u 0
  · by_cases hy : weight y.1 = u 1
    · by_cases hz : weight z.1 = u 2
      · simp [hx, hy, hz, mul_ite]
      · simp [hz]
    · simp [hy]
  · simp [hx]

theorem shape_split_sub {P Q : Type*} [Fintype P] [Fintype Q]
    (g u : Fin 3 → ℕ) (hu : ∀ s, u s ≤ g s)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    (if weight x.1 = u 0 ∧ weight y.1 = u 1 ∧ weight z.1 = u 2 then
      shapeTensor (F := F) (P ⊕ Q) g (Sum.elim x.1 x.2) (Sum.elim y.1 y.2)
        (Sum.elim z.1 z.2) else 0) =
      Tensor.product (shapeTensor P u) (shapeTensor Q (g - u)) x y z := by
  have hg : u + (g - u) = g := by
    funext s
    exact Nat.add_sub_of_le (hu s)
  simpa only [hg] using shape_split u (g - u) x y z

def splitMatrix {P Q : Type*} [Fintype P] (u : ℕ) :
    ((P → Fin 7) × (Q → Fin 7)) → ((P ⊕ Q) → Fin 7) → F := by
  classical
  exact fun x w => if w = Sum.elim x.1 x.2 ∧ weight x.1 = u then 1 else 0

theorem shape_split_restrict {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q] (u v : Fin 3 → ℕ) :
    Tensor.restrict (splitMatrix (F := F) (u 0)) (splitMatrix (u 1)) (splitMatrix (u 2))
      (shapeTensor (P ⊕ Q) (u + v)) =
      Tensor.product (shapeTensor P u) (shapeTensor Q v) := by
  classical
  funext x y z
  have hcollapse : Tensor.restrict (splitMatrix (F := F) (u 0))
      (splitMatrix (u 1)) (splitMatrix (u 2)) (shapeTensor (P ⊕ Q) (u + v)) x y z =
      if weight x.1 = u 0 ∧ weight y.1 = u 1 ∧ weight z.1 = u 2 then
        shapeTensor (P ⊕ Q) (u + v) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2)
          (Sum.elim z.1 z.2) else 0 := by
    simp [Tensor.restrict, splitMatrix, ite_and, ite_mul, mul_ite]
    split_ifs <;> simp_all
  rw [hcollapse]
  exact shape_split u v x y z

end MatrixMultiplication.CWStrands

end

end OAI
