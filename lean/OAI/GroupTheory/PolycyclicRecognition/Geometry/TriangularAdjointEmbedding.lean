import OAI.GroupTheory.PolycyclicRecognition.Geometry.InvariantTriangularBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixLieAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Data.Fin.Rev

namespace OAI

/-!
# A triangular adjoint basis from a faithful triangular representation

Order matrix units by increasing row and decreasing column. Commuting
with an upper triangular matrix then gives an upper triangular operator.
Restricting this action to a faithfully embedded Lie algebra supplies
its actual adjoint basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Rows increase and columns decrease in the ordering of matrix units. -/
def triangularMatrixOrder (n : ℕ) : Fin n × Fin n ≃ Fin (n * n) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) Fin.revPerm).trans finProdFinEquiv

@[simp] theorem triangularMatrixOrder_val {n : ℕ} (p : Fin n × Fin n) :
    (triangularMatrixOrder n p : ℕ) = (p.2.rev : ℕ) + n * (p.1 : ℕ) := rfl

/-- Matrix coordinates with respect to this ordering. -/
def triangularMatrixCoordinates (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] (Fin (n * n) → ℝ) where
  toFun A i := A ((triangularMatrixOrder n).symm i).1
    ((triangularMatrixOrder n).symm i).2
  invFun v i j := v (triangularMatrixOrder n (i, j))
  left_inv A := by ext i j; simp
  right_inv v := by ext i; simp
  map_add' A B := rfl
  map_smul' r A := rfl

@[simp] theorem triangularMatrixCoordinates_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin (n * n)) :
    triangularMatrixCoordinates n A i =
      A ((triangularMatrixOrder n).symm i).1 ((triangularMatrixOrder n).symm i).2 := rfl

@[simp] theorem triangularMatrixCoordinates_symm_apply {n : ℕ}
    (v : Fin (n * n) → ℝ) (i j : Fin n) :
    (triangularMatrixCoordinates n).symm v i j =
      v (triangularMatrixOrder n (i, j)) := rfl

/-- The ordered matrix units. -/
def triangularMatrixBasis (n : ℕ) :
    Basis (Fin (n * n)) ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (Pi.basisFun ℝ (Fin (n * n))).map (triangularMatrixCoordinates n).symm

@[simp] theorem triangularMatrixBasis_apply {n : ℕ} (i j : Fin n) :
    triangularMatrixBasis n (triangularMatrixOrder n (i, j)) = Matrix.single i j 1 := by
  ext k l
  change (triangularMatrixCoordinates n).symm
    ((Pi.basisFun ℝ (Fin (n * n))) (triangularMatrixOrder n (i, j))) k l = _
  rw [Pi.basisFun_apply, triangularMatrixCoordinates_symm_apply]
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    Matrix.single_apply, eq_comm]

@[simp] theorem triangularMatrixBasis_repr_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin (n * n)) :
    (triangularMatrixBasis n).repr A i = triangularMatrixCoordinates n A i := by
  change (Pi.basisFun ℝ (Fin (n * n))).repr (triangularMatrixCoordinates n A) i = _
  simp only [Pi.basisFun_repr]

@[simp] theorem triangularMatrixBasis_repr {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (triangularMatrixBasis n).repr A (triangularMatrixOrder n (i, j)) = A i j := by
  rw [triangularMatrixBasis_repr_apply, triangularMatrixCoordinates_apply]
  simp only [Equiv.symm_apply_apply]

private theorem matrix_commutator_single_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular)
    (p q r s : Fin n)
    (hij : triangularMatrixOrder n (r, s) < triangularMatrixOrder n (p, q)) :
    ((A * Matrix.single r s (1 : ℝ) - Matrix.single r s (1 : ℝ) * A) :
      Matrix (Fin n) (Fin n) ℝ) p q = 0 := by
  rw [Matrix.sub_apply]
  have hleft : (A * Matrix.single r s (1 : ℝ)) p q = 0 := by
    by_cases hqs : q = s
    · subst q
      rw [Matrix.mul_single_apply_same, mul_one]
      apply hA
      have hm : n * (r : ℕ) < n * (p : ℕ) := by
        change (s.rev : ℕ) + n * (r : ℕ) < (s.rev : ℕ) + n * (p : ℕ) at hij
        omega
      change (r : ℕ) < (p : ℕ)
      exact Nat.lt_of_mul_lt_mul_left hm
    · exact Matrix.mul_single_apply_of_ne 1 r s p q hqs A
  have hright : (Matrix.single r s (1 : ℝ) * A) p q = 0 := by
    by_cases hpr : p = r
    · subst p
      rw [Matrix.single_mul_apply_same, one_mul]
      apply hA
      have hrev : s.rev < q.rev := by
        change (s.rev : ℕ) + n * (r : ℕ) < (q.rev : ℕ) + n * (r : ℕ) at hij
        change (s.rev : ℕ) < (q.rev : ℕ)
        omega
      exact Fin.rev_lt_rev.mp hrev
    · exact Matrix.single_mul_apply_of_ne 1 r s p q hpr A
  rw [hleft, hright, sub_self]

/-- Commutation by an upper triangular matrix is upper triangular on
the full matrix algebra in the ordered matrix-unit basis. -/
theorem upperTriangular_matrix_ad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) :
    (LinearMap.toMatrix (triangularMatrixBasis n) (triangularMatrixBasis n)
      (LieAlgebra.ad ℝ (Matrix (Fin n) (Fin n) ℝ) A)).IsUpperTriangular := by
  intro i j hij
  obtain ⟨⟨p, q⟩, rfl⟩ := (triangularMatrixOrder n).surjective i
  obtain ⟨⟨r, s⟩, rfl⟩ := (triangularMatrixOrder n).surjective j
  rw [LinearMap.toMatrix_apply, triangularMatrixBasis_apply,
    LieAlgebra.ad_apply, LieRing.of_associative_ring_bracket,
    triangularMatrixBasis_repr]
  exact matrix_commutator_single_zero A hA p q r s hij

/-- A faithful triangular matrix representation produces the precise
simultaneous adjoint basis used by the height development. -/
theorem nonempty_triangularAdjoint_of_triangular_representation
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    {n : ℕ} (ρ : L →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℝ)
    (hρ : Function.Injective ρ) (htri : ∀ x, (ρ x).IsUpperTriangular) :
    ∃ m : ℕ, Nonempty (TriangularAdjoint L m) := by
  let b := triangularMatrixBasis n
  let e : L →ₗ[ℝ] (Fin (n * n) → ℝ) :=
    (triangularMatrixCoordinates n).toLinearMap.comp ρ.toLinearMap
  let T := LieAlgebra.ad ℝ L
  let A (x : L) := LinearMap.toMatrix b b
    (LieAlgebra.ad ℝ (Matrix (Fin n) (Fin n) ℝ) (ρ x))
  have he : Function.Injective e :=
    (triangularMatrixCoordinates n).injective.comp hρ
  have hA : ∀ x, (A x).IsUpperTriangular := fun x =>
    upperTriangular_matrix_ad (ρ x) (htri x)
  have hinter : ∀ x v, e (T x v) = A x *ᵥ e v := by
    intro x v
    have hc := LinearMap.toMatrix_mulVec_repr b b
      (LieAlgebra.ad ℝ (Matrix (Fin n) (Fin n) ℝ) (ρ x)) (ρ v)
    have hm : ρ (T x v) = ⁅ρ x, ρ v⁆ := ρ.map_lie x v
    have hcoord (M : Matrix (Fin n) (Fin n) ℝ) :
        ⇑(b.repr M) = triangularMatrixCoordinates n M :=
      funext fun i => triangularMatrixBasis_repr_apply M i
    rw [hcoord, hcoord] at hc
    change triangularMatrixCoordinates n (ρ (T x v)) =
      A x *ᵥ triangularMatrixCoordinates n (ρ v)
    rw [hm]
    exact hc.symm
  obtain ⟨m, bL, hbL⟩ := exists_upperTriangular_basis_of_embedding e he T A hA hinter
  exact ⟨m, ⟨⟨bL, hbL⟩⟩⟩

end PolycyclicRecognition

end

end OAI
