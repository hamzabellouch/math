import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Solvable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Solvability of a faithful triangular matrix representation

Successive derived algebras vanish on successively larger bands above
the diagonal. This proves the solvability needed after differentiating
a triangular Lie-group realization, without assuming that passage from
the group to its Lie algebra.
-/

noncomputable section

namespace PolycyclicRecognition

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Matrices whose entries vanish below the `k`th upper diagonal. -/
def matrixUpperGap (n k : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | ∀ i j : Fin n, (j : ℕ) < (i : ℕ) + k → A i j = 0}
  zero_mem' := by simp
  add_mem' hA hB := by
    intro i j hij
    simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]
  smul_mem' r A hA := by
    intro i j hij
    simp only [Matrix.smul_apply, hA i j hij, smul_zero]

theorem matrixUpperGap_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ matrixUpperGap n 0 ↔ A.IsUpperTriangular := by
  constructor
  · intro h i j hij
    exact h i j (by change (j : ℕ) < (i : ℕ) at hij; simpa using hij)
  · intro h i j hij
    exact h (by change (j : ℕ) < (i : ℕ); simpa using hij)

theorem matrixUpperGap_anti {n a b : ℕ} (hab : a ≤ b) :
    matrixUpperGap n b ≤ matrixUpperGap n a := by
  intro A hA i j hij
  exact hA i j (by omega)

theorem matrixUpperGap_mul {n a b : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ matrixUpperGap n a) (hB : B ∈ matrixUpperGap n b) :
    A * B ∈ matrixUpperGap n (a + b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : (t : ℕ) < (i : ℕ) + a
  · rw [hA i t ht, zero_mul]
  · rw [hB t j (by omega), mul_zero]

private theorem upperTriangular_mul_diagonal {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

/-- A commutator improves the vanishing band by at least one. -/
theorem matrixUpperGap_lie {n k : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ matrixUpperGap n k) (hB : B ∈ matrixUpperGap n k) :
    ⁅A, B⁆ ∈ matrixUpperGap n (k + 1) := by
  by_cases hk : k = 0
  · subst k
    have hAt := (matrixUpperGap_zero_iff A).mp hA
    have hBt := (matrixUpperGap_zero_iff B).mp hB
    intro i j hij
    change (A * B - B * A) i j = 0
    rw [Matrix.sub_apply]
    by_cases hji : j = i
    · subst j
      rw [upperTriangular_mul_diagonal hAt hBt,
        upperTriangular_mul_diagonal hBt hAt, mul_comm, sub_self]
    · have hlt : j < i := by
        have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
        change (j : ℕ) < (i : ℕ)
        omega
      rw [hAt.mul hBt hlt, hBt.mul hAt hlt, sub_self]
  · have hAB := matrixUpperGap_mul hA hB
    have hBA := matrixUpperGap_mul hB hA
    exact matrixUpperGap_anti (by omega : k + 1 ≤ k + k)
      ((matrixUpperGap n (k + k)).sub_mem hAB hBA)

/-- A faithful finite-dimensional triangular representation has a
solvable Lie algebra. The proof uses actual matrix entries, not a
solvability assumption about the source group. -/
theorem lieAlgebra_isSolvable_of_triangular_representation
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
    (ρ : L →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℝ)
    (hρ : Function.Injective ρ) (htri : ∀ x, (ρ x).IsUpperTriangular) :
    LieAlgebra.IsSolvable L := by
  have hderived : ∀ k, ∀ x ∈ LieAlgebra.derivedSeries ℝ L k,
      ρ x ∈ matrixUpperGap n k := by
    intro k
    induction k with
    | zero =>
      intro x _
      exact (matrixUpperGap_zero_iff (ρ x)).mpr (htri x)
    | succ k ih =>
      intro x hx
      change x ∈ (LieAlgebra.derivedSeries ℝ L (k + 1)).toSubmodule at hx
      rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
        LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
      change x ∈ Submodule.span ℝ
        {⁅a, b⁆ | (a ∈ LieAlgebra.derivedSeries ℝ L k)
          (b ∈ LieAlgebra.derivedSeries ℝ L k)} at hx
      exact (Submodule.span_le.mpr (by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        change ρ ⁅a, b⁆ ∈ matrixUpperGap n (k + 1)
        rw [ρ.map_lie]
        exact matrixUpperGap_lie (ih a ha) (ih b hb)) hx :
          x ∈ (matrixUpperGap n (k + 1)).comap ρ.toLinearMap)
  apply LieAlgebra.IsSolvable.mk (R := ℝ) (k := n)
  apply le_antisymm _ bot_le
  intro x hx
  have hg := hderived n x hx
  have hz : ρ x = 0 := by
    ext i j
    exact hg i j (by have := j.isLt; omega)
  exact (LieSubmodule.mem_bot x).mpr (hρ (hz.trans (map_zero ρ).symm))

end PolycyclicRecognition

end

end OAI
