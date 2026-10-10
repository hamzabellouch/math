import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.HermitianMat

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

def operatorNorm (A : H d) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A : Mat d)‖

lemma operatorNorm_nonneg (A : H d) : 0 ≤ operatorNorm A := norm_nonneg _

lemma operatorNorm_eq_matrix (A : H d) : operatorNorm A = ‖(A : Mat d)‖ := rfl

lemma scalarOne_eq_algebraMap (r : ℝ) : ((r • (one : H d) : H d) : Mat d) = algebraMap ℝ (Mat d) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

lemma operatorNorm_le_of_bounds {A : H d} {r : ℝ} (hr : 0 ≤ r)
    (hlo : -r • (one : H d) ≤ A) (hhi : A ≤ r • (one : H d)) : operatorNorm A ≤ r := by
  let : CStarAlgebra (Mat d) := {}
  by_cases htriv : Subsingleton (Mat d)
  · let := htriv
    rw [operatorNorm_eq_matrix,Subsingleton.elim (A : Mat d) 0,norm_zero]
    exact hr
  · have : Nontrivial (Mat d) := not_subsingleton_iff_nontrivial.mp htriv
    have hh : (A : Mat d) ≤ algebraMap ℝ (Mat d) r := by
      change (A : Mat d) ≤ ((r • one : H d) : Mat d) at hhi
      rwa [scalarOne_eq_algebraMap] at hhi
    have hl : algebraMap ℝ (Mat d) (-r) ≤ (A : Mat d) := by
      change ((-r • one : H d) : Mat d) ≤ (A : Mat d) at hlo
      rwa [scalarOne_eq_algebraMap] at hlo
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (A : Mat d) A.property.isSelfAdjoint with hn | hn
    · exact (le_algebraMap_iff_spectrum_le A.property.isSelfAdjoint).mp hh _ hn
    · have h := (algebraMap_le_iff_le_spectrum A.property.isSelfAdjoint).mp hl _ hn
      change ‖(A : Mat d)‖ ≤ r
      linarith

lemma le_operatorNorm_smul_one (A : H d) : A ≤ operatorNorm A • one := by
  let : CStarAlgebra (Mat d) := {}
  change (A : Mat d) ≤ ((operatorNorm A • one : H d) : Mat d)
  rw [scalarOne_eq_algebraMap,operatorNorm_eq_matrix]
  exact A.property.isSelfAdjoint.le_algebraMap_norm_self

lemma operatorNorm_le_of_psd_le {A : H d} (hA : A ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hhi : A ≤ r • (one : H d)) : operatorNorm A ≤ r := by
  let : CStarAlgebra (Mat d) := {}
  apply (CStarAlgebra.norm_le_iff_le_algebraMap (A : Mat d) hr hA.nonneg).mpr
  change (A : Mat d) ≤ ((r • one : H d) : Mat d) at hhi
  rwa [scalarOne_eq_algebraMap] at hhi

lemma operatorNorm_eq_zero_iff (A : H d) : operatorNorm A = 0 ↔ A = 0 := by
  rw [operatorNorm_eq_matrix,norm_eq_zero]
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

lemma operatorNorm_smul (r : ℝ) (A : H d) : operatorNorm (r • A) = |r| * operatorNorm A := by
  change ‖(r : ℂ) • (A : Mat d)‖ = _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  rfl

end

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma operatorNorm_le_frobenius (A : H d) : operatorNorm A ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  have hm := Matrix.frobenius_norm_mul (A : Mat d) (Matrix.replicateCol (Fin 1) (WithLp.ofLp v))
  rw [← Matrix.replicateCol_mulVec] at hm
  have hn (w : Fin d → ℂ) : ‖Matrix.replicateCol (Fin 1) w‖ = ‖WithLp.toLp 2 w‖ := by
    simp [Matrix.frobenius_norm_def, Matrix.replicateCol_apply, PiLp.norm_eq_of_L2,
      Real.sqrt_eq_rpow]
  rw [hn,hn] at hm
  exact hm

lemma scalar_one_mono_frob {r s : ℝ} (h : r ≤ s) :
    r • (one : H d) ≤ s • one := by
  apply sub_nonneg.mp
  erw [← sub_smul]
  change (0 : Mat d) ≤ ((s-r : ℝ) • (1 : Mat d))
  exact (Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr h :
    (0 : ℂ) ≤ ((s-r : ℝ) : ℂ))).nonneg

lemma le_norm_smul_one (A : H d) : A ≤ ‖A‖ • one :=
  (le_operatorNorm_smul_one A).trans (scalar_one_mono_frob (operatorNorm_le_frobenius A))

lemma neg_norm_smul_one_le (A : H d) : -‖A‖ • one ≤ A := by
  have h := le_norm_smul_one (-A)
  rw [norm_neg] at h
  have hh := neg_le_neg h
  simp only [neg_neg] at hh
  convert hh using 1; first | rfl | module

lemma ball_order_bounds (A B : H d) {r : ℝ} (h : ‖A-B‖ ≤ r) :
    B-r • one ≤ A ∧ A ≤ B+r • one := by
  have hi : A-B ≤ r • one :=
    (le_norm_smul_one (A-B)).trans (scalar_one_mono_frob h)
  have hl : -r • one ≤ A-B :=
    (scalar_one_mono_frob (neg_le_neg h)).trans (neg_norm_smul_one_le (A-B))
  constructor
  · have hle := add_le_add_right hl B
    convert hle using 1 <;> first | rfl | module
  · exact sub_le_iff_le_add.mp hi |>.trans_eq (add_comm _ _)

end CurrentKS.Hermitian

end

end OAI
