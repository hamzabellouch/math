import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFalconer
open Finset

theorem row_weight_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → Prop) [DecidableRel G] (u : ι → ℝ) :
    (∑ i, ∑ j, if G i j then u i else 0) =
      ∑ i, ((Finset.univ.filter (G i)).card : ℝ)*u i := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem bipartite_schur {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → Prop) [DecidableRel G] (u : ι → ℝ) (v : κ → ℝ) (d : ℝ)
    (hrow : ∀ i, ((Finset.univ.filter (G i)).card : ℝ) ≤ d)
    (hcol : ∀ j, ((Finset.univ.filter (fun i => G i j)).card : ℝ) ≤ d) :
    (∑ i, ∑ j, if G i j then u i*v j else 0) ≤
      d/2*((∑ i, u i^2)+(∑ j, v j^2)) := by
  have hpoint : ∀ i j, 2*(if G i j then u i*v j else 0) ≤
      (if G i j then u i^2 else 0)+(if G i j then v j^2 else 0) := by
    intro i j
    split_ifs
    · nlinarith [sq_nonneg (u i-v j)]
    · norm_num
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hR : (∑ i, ∑ j, if G i j then u i^2 else 0) ≤ d*(∑ i, u i^2) := by
    rw [row_weight_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  have hC : (∑ i, ∑ j, if G i j then v j^2 else 0) ≤ d*(∑ j, v j^2) := by
    rw [Finset.sum_comm, row_weight_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
  nlinarith

theorem bipartite_schur_abs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → Prop) [DecidableRel G] (u : ι → ℝ) (v : κ → ℝ) (d : ℝ)
    (hrow : ∀ i, ((Finset.univ.filter (G i)).card : ℝ) ≤ d)
    (hcol : ∀ j, ((Finset.univ.filter (fun i => G i j)).card : ℝ) ≤ d) :
    (∑ i, ∑ j, if G i j then |u i*v j| else 0) ≤
      d/2*((∑ i, u i^2)+(∑ j, v j^2)) := by
  simpa only [abs_mul, sq_abs] using bipartite_schur G (fun i => |u i|) (fun j => |v j|) d hrow hcol

end PlanarFalconer

end OAI
