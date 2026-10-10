import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace SiegelZeros


noncomputable section
open scoped BigOperators
open InnerProductSpace

namespace WeightedTorusJets.W35

theorem norm_det_le_prod_row_norm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin m))‖ := by
  let v : Fin m → EuclideanSpace ℂ (Fin m) := fun i => WithLp.toLp 2 (A i)
  let e := EuclideanSpace.basisFun (Fin m) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by
    simp
  let b := gramSchmidtOrthonormalBasis hdim v
  have he : e.toBasis.det v = A.transpose.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have hchange : e.toBasis.det v = e.toBasis.det b * b.toBasis.det v := by
    have h := congrArg (fun f : (EuclideanSpace ℂ (Fin m)) [⋀^Fin m]→ₗ[ℂ] ℂ => f v)
      (e.toBasis.det.eq_smul_basis_det b.toBasis)
    simpa using h
  have hnorm : ‖e.toBasis.det v‖ = ‖b.toBasis.det v‖ := by
    rw [hchange, norm_mul, e.det_to_matrix_orthonormalBasis b, one_mul]
  rw [← Matrix.det_transpose, ← he, hnorm]
  rw [show b.toBasis.det v = ∏ i, inner ℂ (b i) (v i) from
    gramSchmidtOrthonormalBasis_det hdim v, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  simpa only [b.norm_eq_one, one_mul] using norm_inner_le_norm (b i) (v i)

theorem norm_det_le_prod_row_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (hA : ∀ i j, ‖A i j‖ ≤ r i) :
    ‖A.det‖ ≤ ∏ i, (Real.sqrt m * r i) := by
  apply (norm_det_le_prod_row_norm A).trans
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ j, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin m)) j‖ ^ 2)
        ≤ Real.sqrt (∑ _j : Fin m, (r i)^2) := by
          apply Real.sqrt_le_sqrt
          exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
    _ = Real.sqrt m * r i := by simp [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (hr i)]

theorem log_norm_det_le {m : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin m) ℂ)
    (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (hA : ∀ i j, ‖A i j‖ ≤ r i)
    (hne : A.det ≠ 0) :
    Real.log ‖A.det‖ ≤ (m : ℝ) / 2 * Real.log m + ∑ i, Real.log (r i) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmp
  have hbound := norm_det_le_prod_row_bound A r (fun i => (hr i).le) hA
  have hlog := Real.log_le_log (norm_pos_iff.mpr hne) hbound
  rw [Real.log_prod (fun i _ => mul_ne_zero hs.ne' (hr i).ne')] at hlog
  simp_rw [Real.log_mul hs.ne' (hr _).ne', Real.log_sqrt hmp.le] at hlog
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_div_assoc, div_mul_eq_mul_div] using hlog

def eigenvalueMatrix {m : ℕ} (z : Fin 3 → Fin m → ℂ) (a : Fin m → Fin 3 → ℕ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => z 0 j ^ a i 0 * z 1 j ^ a i 1 * z 2 j ^ a i 2

theorem eigenvalueMatrix_entry_bound {m : ℕ}
    (z : Fin 3 → Fin m → ℂ) (a : Fin m → Fin 3 → ℕ)
    (B : ℝ) (hB : 0 ≤ B) (hz : ∀ k j, ‖z k j‖ ≤ B) (i j : Fin m) :
    ‖eigenvalueMatrix z a i j‖ ≤ B ^ (a i 0 + a i 1 + a i 2) := by
  simp only [eigenvalueMatrix, norm_mul, norm_pow, pow_add]
  exact mul_le_mul
    (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hz 0 j) _)
      (pow_le_pow_left₀ (norm_nonneg _) (hz 1 j) _) (by positivity) (by positivity))
    (pow_le_pow_left₀ (norm_nonneg _) (hz 2 j) _) (by positivity) (by positivity)

theorem log_norm_eigenvalueMatrix_det_le {m : ℕ} (hm : 0 < m)
    (z : Fin 3 → Fin m → ℂ) (a : Fin m → Fin 3 → ℕ)
    (B : ℝ) (hB : 0 < B) (hz : ∀ k j, ‖z k j‖ ≤ B)
    (hne : (eigenvalueMatrix z a).det ≠ 0) :
    Real.log ‖(eigenvalueMatrix z a).det‖ ≤
      (m : ℝ) / 2 * Real.log m +
      (∑ i, ((a i 0 + a i 1 + a i 2 : ℕ) : ℝ)) * Real.log B := by
  have h := log_norm_det_le hm (eigenvalueMatrix z a)
    (fun i => B ^ (a i 0 + a i 1 + a i 2)) (fun _ => pow_pos hB _)
    (eigenvalueMatrix_entry_bound z a B hB.le hz) hne
  simpa only [Real.log_pow, Finset.sum_mul] using h

end WeightedTorusJets.W35

end


end SiegelZeros

end OAI
