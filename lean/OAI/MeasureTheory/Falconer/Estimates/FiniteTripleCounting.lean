import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI

/-! # The finite three-coordinate counting inequality for endpoint slices -/

namespace Falconer
open scoped BigOperators
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

theorem finite_triangle_square_bound (f : X → Y → ℝ) (g : Y → Z → ℝ) (h : Z → X → ℝ) :
    (∑ x, ∑ y, ∑ z, f x y*g y z*h z x)^2 ≤
      (∑ x, ∑ y, (f x y)^2)*(∑ y, ∑ z, (g y z)^2)*(∑ z, ∑ x, (h z x)^2) := by
  let G : Y → ℝ := fun y => ∑ z, (g y z)^2
  let H : X → ℝ := fun x => ∑ z, (h z x)^2
  have hrow (x : X) (y : Y) : (∑ z, g y z*h z x)^2 ≤ G y*H x :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun z => g y z) (fun z => h z x)
  have hrows : (∑ x, ∑ y, (∑ z, g y z*h z x)^2) ≤ (∑ y, G y)*(∑ x, H x) := by
    calc
      _ ≤ ∑ x, ∑ y, G y*H x :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hrow x y))
      _ = _ := by simp only [← Finset.sum_mul,← Finset.mul_sum]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : X × Y => f p.1 p.2) (fun p : X × Y => ∑ z, g p.2 z*h z p.1)
  simp only [Fintype.sum_prod_type] at hCS
  have hnonneg : 0 ≤ ∑ x, ∑ y, (f x y)^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hh := hCS.trans (mul_le_mul_of_nonneg_left hrows hnonneg)
  convert hh using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  · dsimp [G,H]
    rw [Finset.sum_comm (f := fun x : X => fun z : Z => (h z x)^2)]
    ring

end Falconer

end OAI
