import Mathlib
import OAI.Analysis.MatrixSigning.Potential.CovarianceE

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

local instance columnInnerProductSpace : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {m n : ℕ}

lemma trace_mul_nonneg {Q Γ : Mat m} (hQ : Q.PosSemidef) (hΓ : Γ.PosSemidef) :
    0 ≤ (Q*Γ).trace := by
  have hS : (CFC.sqrt Γ).IsHermitian := (CFC.sqrt_nonneg Γ).posSemidef.isHermitian
  have hp := (hQ.conjTranspose_mul_mul_same (CFC.sqrt Γ)).trace_nonneg
  rw [hS.eq,Matrix.trace_mul_cycle,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg,Matrix.trace_mul_comm] at hp
  exact hp

lemma trace_mul_diagonal_eq (Q : Mat m) (a : Fin m → ℝ) :
    (Q*Matrix.diagonal a).trace = ∑ i, Q i i*a i := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal]

lemma energy_trace_domination (Q Γ : Mat m) (hQ : Q.PosSemidef) {κ : ℝ}
    (hΓ : (κ • Matrix.diagonal (Matrix.diag Γ)-Γ).PosSemidef) :
    (Q*Γ).trace ≤ κ*(∑ i, Q i i*Γ i i) := by
  have hp := trace_mul_nonneg hQ hΓ
  rw [mul_sub,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,
    trace_mul_diagonal_eq] at hp
  exact sub_nonneg.mp hp

lemma sqrt_range_eq {Γ : Mat m} (hΓ : Γ.PosSemidef) :
    (CFC.sqrt Γ).toEuclideanLin.range = Γ.toEuclideanLin.range := by
  have hS : (CFC.sqrt Γ).IsHermitian := (CFC.sqrt_nonneg Γ).posSemidef.isHermitian
  have hr := LinearMap.range_self_comp_adjoint (CFC.sqrt Γ).toEuclideanLin
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hS.eq,← toEuclideanLin_mul,
    CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg] at hr
  exact hr.symm

lemma on_sqrt_range {Γ : Mat m} (hΓ : Γ.PosSemidef) (P : E m → Prop)
    (hP : ∀ x, P (Γ.toEuclideanLin x)) : ∀ x, P ((CFC.sqrt Γ).toEuclideanLin x) := by
  intro x
  have hr : (CFC.sqrt Γ).toEuclideanLin x ∈ Γ.toEuclideanLin.range := by
    rw [← sqrt_range_eq hΓ]
    exact ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hr
  rw [← hy]
  exact hP y

def column (A : Mat m) (j : Fin m) : E m := toLp 2 (fun i => A i j)

lemma column_eq_apply_basis (A : Mat m) (j : Fin m) :
    column A j = A.toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ j) := by
  ext i
  simp [column,Matrix.toLpLin_apply,EuclideanSpace.basisFun_apply,Matrix.mulVec_single]

lemma sqrt_column_range {Γ : Mat m} (hΓ : Γ.PosSemidef) (P : E m → Prop)
    (hP : ∀ x, P (Γ.toEuclideanLin x)) (j : Fin m) : P (column (CFC.sqrt Γ) j) := by
  rw [column_eq_apply_basis]
  exact on_sqrt_range hΓ P hP _

lemma sum_column_quadratic (Q C : Mat m) :
    (∑ j, quad Q (column C j)) = (C.conjTranspose*Q*C).trace := by
  simp only [quad,column,Matrix.toLpLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,Matrix.mulVec,dotProduct,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma sqrt_moments {Γ : Mat m} (hΓ : Γ.PosSemidef) (Q : Mat m) :
    (∑ j, quad Q (column (CFC.sqrt Γ) j)) = (Q*Γ).trace := by
  rw [sum_column_quadratic,(CFC.sqrt_nonneg Γ).posSemidef.isHermitian.eq,
    Matrix.trace_mul_cycle,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg,Matrix.trace_mul_comm]

lemma row_moments {Γ : Mat m} (hΓ : Γ.PosSemidef) (i : Fin m) :
    (∑ j, (column (CFC.sqrt Γ) j i)^2) = Γ i i := by
  have hS : (CFC.sqrt Γ).IsHermitian := (CFC.sqrt_nonneg Γ).posSemidef.isHermitian
  have hh := congrArg (fun A : Mat m => A i i) (CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg)
  try dsimp only at hh
  rw [Matrix.mul_apply] at hh
  have hs : ∀ j, CFC.sqrt Γ j i = CFC.sqrt Γ i j := by
    intro j
    have he := congrArg (fun A : Mat m => A i j) hS.eq
    simpa only [Matrix.conjTranspose_apply,star_trivial] using he
  simpa only [hs,column,sq] using hh

lemma total_movement {Γ : Mat m} (hΓ : Γ.PosSemidef) :
    (∑ j, ‖column (CFC.sqrt Γ) j‖^2) = Γ.trace := by
  have h := sqrt_moments hΓ (1 : Mat m)
  simpa only [quad,Matrix.toLpLin_one,LinearMap.id_apply,real_inner_self_eq_norm_sq,one_mul] using h

end
end CurrentKS.Covariance

end OAI
