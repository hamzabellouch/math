import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
import Mathlib.Tactic.SplitIfs

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.Replication

variable {K I R X Y Z X' Y' Z' : Type*} [CommSemiring K]

theorem restrict_directSum
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    (T : I → Tensor K X Y Z)
    (a : I → X' → X → K) (b : I → Y' → Y → K) (c : I → Z' → Z → K) :
    Tensor.restrict
      (fun x s => if x.1 = s.1 then a x.1 x.2 s.2 else 0)
      (fun y s => if y.1 = s.1 then b y.1 y.2 s.2 else 0)
      (fun z s => if z.1 = s.1 then c z.1 z.2 s.2 else 0)
      (Tensor.directSum T) = Tensor.directSum (fun i => Tensor.restrict (a i) (b i) (c i) (T i)) := by
  classical
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
        ite_and, ite_mul, mul_ite]
    · simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
        ite_and, ite_mul, mul_ite, hik]
  · simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
      ite_and, ite_mul, mul_ite, hij]
    intro hjk hik
    exact (hij (hik.trans hjk.symm)).elim

theorem swap_replication [DecidableEq I] [DecidableEq R]
    (T : I → Tensor K X Y Z) :
    Tensor.pullback
      (fun x : I × (R × X) => (x.2.1, (x.1, x.2.2)))
      (fun y : I × (R × Y) => (y.2.1, (y.1, y.2.2)))
      (fun z : I × (R × Z) => (z.2.1, (z.1, z.2.2)))
      (Tensor.directSum (fun _ : R => Tensor.directSum T)) =
      Tensor.directSum (fun i => Tensor.directSum (fun _ : R => T i)) := by
  funext x y z
  simp only [Tensor.pullback, Tensor.directSum]
  split_ifs <;> simp_all

theorem repair_branches
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : I → Tensor K X Y Z) (Q : I → Tensor K X' Y' Z')
    (a : I → X' → (R × X) → K) (b : I → Y' → (R × Y) → K)
    (c : I → Z' → (R × Z) → K)
    (h : ∀ i, Tensor.restrict (a i) (b i) (c i)
      (Tensor.directSum (fun _ : R => T i)) = Q i) :
    ∃ (A : (I × X') → (R × (I × X)) → K)
      (B : (I × Y') → (R × (I × Y)) → K)
      (C : (I × Z') → (R × (I × Z)) → K),
      Tensor.restrict A B C (Tensor.directSum (fun _ : R => Tensor.directSum T)) =
        Tensor.directSum Q := by
  classical
  have hb := restrict_directSum (fun i => Tensor.directSum (fun _ : R => T i)) a b c
  simp_rw [h] at hb
  rw [← swap_replication T, Tensor.pullback_eq_restrict, Tensor.restrict_restrict] at hb
  exact ⟨_, _, _, hb⟩

end MatrixMultiplication.Replication

end OAI
