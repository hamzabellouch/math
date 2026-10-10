import OAI.LinearAlgebra.MatrixMultiplication.Recovery.Staggering
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.PhysicalOrders

open Staggering

abbrev PhysicalOrder := Equiv.Perm (Fin 3)

theorem card_physical_orders : Fintype.card PhysicalOrder = 6 := by
  norm_num [PhysicalOrder, Fintype.card_perm, Nat.factorial_succ]

def placementAmount (amount : ℝ) (_phi : PhysicalOrder) : ℝ := amount / 6

theorem placementAmount_eq (amount : ℝ) (phi psi : PhysicalOrder) :
    placementAmount amount phi = placementAmount amount psi := rfl

theorem sum_placementAmount (amount : ℝ) :
    ∑ phi : PhysicalOrder, placementAmount amount phi = amount := by
  simp only [placementAmount, Finset.sum_const, Finset.card_univ,
    card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

theorem placement_has_unique_order (rho phi : PhysicalOrder) :
    ∃! sigma : PhysicalOrder, rho.trans phi = sigma := by
  refine ⟨rho.trans phi, rfl, ?_⟩
  intro sigma hsigma
  exact hsigma.symm

theorem sum_selected_placement (rho sigma : PhysicalOrder) (value : ℝ) :
    (∑ phi : PhysicalOrder, if rho.trans phi = sigma then value else 0) = value := by
  classical
  obtain ⟨phi, hphi, hunique⟩ := physical_order_unique rho sigma
  calc
    _ = ∑ psi : PhysicalOrder, if psi = phi then value else 0 := by
      apply Finset.sum_congr rfl
      intro psi _
      have hiff : rho.trans psi = sigma ↔ psi = phi := by
        constructor
        · exact hunique psi
        · rintro rfl
          exact hphi
      simp only [hiff]
    _ = value := by simp

variable {History : Type*} [Fintype History]

def aggregateCapacity (amount : History → ℝ) (capacity : History → Capacity) : Capacity :=
  fun i => ∑ h, amount h * capacity h i

def perPhysicalOrderCapacity (amount : History → ℝ) (capacity : History → Capacity)
    (priority : History → PhysicalOrder) (sigma : PhysicalOrder) : Capacity := by
  classical
  exact fun i => ∑ h, ∑ phi : PhysicalOrder,
    if (priority h).trans phi = sigma then amount h / 6 * capacity h i else 0

theorem perPhysicalOrderCapacity_apply (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder)
    (sigma : PhysicalOrder) (i : Fin 3) :
    perPhysicalOrderCapacity amount capacity priority sigma i =
      (1 / 6 : ℝ) * aggregateCapacity amount capacity i := by
  classical
  unfold perPhysicalOrderCapacity aggregateCapacity
  simp only [sum_selected_placement]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem perPhysicalOrderCapacity_eq (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder)
    (sigma : PhysicalOrder) :
    perPhysicalOrderCapacity amount capacity priority sigma =
      fun i => (1 / 6 : ℝ) * aggregateCapacity amount capacity i := by
  funext i
  exact perPhysicalOrderCapacity_apply amount capacity priority sigma i

theorem minCapacity_mul (a : Capacity) (r : ℝ) (hr : 0 ≤ r) :
    minCapacity (fun i => r * a i) = r * minCapacity a := by
  unfold minCapacity
  rw [mul_min_of_nonneg _ _ hr, mul_min_of_nonneg _ _ hr]

theorem sum_physical_order_minima (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder) :
    (∑ sigma : PhysicalOrder,
      minCapacity (perPhysicalOrderCapacity amount capacity priority sigma)) =
        minCapacity (aggregateCapacity amount capacity) := by
  simp_rw [perPhysicalOrderCapacity_eq,
    minCapacity_mul _ (1 / 6 : ℝ) (by norm_num)]
  simp only [Finset.sum_const, Finset.card_univ, card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

end MatrixMultiplication.PhysicalOrders

end

end OAI
