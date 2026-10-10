import OAI.Analysis.HyperbolicCones.MatrixBasic

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix

universe u

namespace Paper256

def phiLinear {R : Type u} [CommRing R] (y : Fin 3 → R) : Mat 4 R →ₗ[R] Mat 4 R where
  toFun := phi y
  map_add' := phi_add y
  map_smul' := phi_smul y

theorem phi_isHermitian (y : Fin 3 → ℝ) (X : Mat 4 ℝ) (hX : X.IsHermitian) :
    (phi y X).IsHermitian := by
  have hQ (i j : Fin 3) : qMatrix y j i = qMatrix y i j := by
    by_cases h : i = j
    · subst j; rfl
    · simp [qMatrix, h, Ne.symm h, mul_comm]
  have hXs (i j : Fin 4) : X j i = X i j := by simpa using hX.apply i j
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · simp only [phi, Fin.cases_zero, Fin.cases_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ, hXs 0 k.succ]
    ring
  · simp only [phi, Fin.cases_zero, Fin.cases_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ, hXs 0 k.succ]
    ring
  · simp only [phi, Fin.cases_succ]
    rw [hQ]

theorem posSemidef_sum_outer {n : ℕ} (X : Mat n ℝ) (hX : X.PosSemidef) :
    ∃ v : Fin n → Vec n, X = ∑ i, outer (v i) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  refine ⟨fun i => WithLp.toLp 2 (B i), ?_⟩
  rw [hB]
  ext i j
  simp [Matrix.mul_apply, Matrix.sum_apply, outer]

end Paper256

end

end OAI
