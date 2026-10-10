import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.TraceCLM
import OAI.Analysis.MatrixSigning.Matrices.Sandwich
import OAI.Analysis.MatrixSigning.Matrices.RealTrace

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_mono_right_psd (A : H d) (hA : A ∈ psdCone d) {B C : H d} (hBC : B ≤ C) :
    inner ℝ A B ≤ inner ℝ A C := by
  have hh := inner_nonneg_of_psd A (C-B) hA ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hBC))
  rw [inner_sub_right] at hh
  linarith

lemma inner_le_trace_mul_trace (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    inner ℝ A B ≤ realTrace A * realTrace B := by
  have hh := inner_mono_right_psd A hA (trace_bound_above hB)
  rw [real_inner_smul_right A (one : H d) (realTrace B),inner_one'] at hh
  nlinarith

lemma sandwich_inverse_left (X A : H d) (hX : X ∈ pd d) :
    sandwich X (sandwich (invH X) A) = A := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change (X : Mat d)*((X : Mat d)⁻¹*(A : Mat d)*(X : Mat d)⁻¹)*(X : Mat d) = (A : Mat d)
  simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hx,one_mul]
  rw [mul_assoc,Matrix.nonsing_inv_mul _ hx,mul_one]

lemma sandwich_inverse_right (X A : H d) (hX : X ∈ pd d) :
    sandwich (invH X) (sandwich X A) = A := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change (X : Mat d)⁻¹*((X : Mat d)*(A : Mat d)*(X : Mat d))*(X : Mat d)⁻¹ = (A : Mat d)
  simp only [← mul_assoc, Matrix.nonsing_inv_mul _ hx,one_mul]
  rw [mul_assoc,Matrix.mul_nonsing_inv _ hx,mul_one]

section SquareRoot
open scoped Matrix.Norms.L2Operator

lemma exists_psd_square (X : H d) (hX : X ∈ psdCone d) :
    ∃ R : H d, R ∈ psdCone d ∧ (R : Mat d)*(R : Mat d) = (X : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have hr : (CFC.sqrt (X : Mat d)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  exact ⟨⟨CFC.sqrt (X : Mat d),hr.isHermitian⟩,hr,CFC.sqrt_mul_sqrt_self _ hX.nonneg⟩
end SquareRoot

lemma inner_sandwich_square (R A B : H d) :
    inner ℝ (sandwich R A) (sandwich R B) = inner ℝ A (sandwich (sandwich R one) B) := by
  rw [inner_eq_trace,inner_eq_trace]
  change (((R : Mat d)*(A : Mat d)*(R : Mat d))*((R : Mat d)*(B : Mat d)*(R : Mat d))).trace.re =
    ((A : Mat d)*(((R : Mat d)*1*(R : Mat d))*(B : Mat d)*((R : Mat d)*1*(R : Mat d)))).trace.re
  simp only [mul_one]
  simp only [mul_assoc]
  rw [Matrix.trace_mul_comm (R : Mat d)]
  simp only [mul_assoc]

lemma sandwich_inner_nonneg (X A : H d) (hX : X ∈ psdCone d) :
    0 ≤ inner ℝ A (sandwich X A) := by
  obtain ⟨R,hR,hRX⟩ := exists_psd_square X hX
  have he : sandwich R one = X := by
    apply Subtype.ext
    change (R : Mat d)*1*(R : Mat d) = (X : Mat d)
    simpa only [mul_one] using hRX
  rw [← he,← inner_sandwich_square]
  exact real_inner_self_nonneg

lemma inner_sandwich_le (X A B : H d) (hX : X ∈ psdCone d)
    (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    inner ℝ A (sandwich X B) ≤ inner ℝ A X * inner ℝ B X := by
  obtain ⟨R,hR,hRX⟩ := exists_psd_square X hX
  have he : sandwich R one = X := by
    apply Subtype.ext
    change (R : Mat d)*1*(R : Mat d) = (X : Mat d)
    simpa only [mul_one] using hRX
  have hh := inner_le_trace_mul_trace (sandwich R A) (sandwich R B)
    (sandwich_psd _ _ hA) (sandwich_psd _ _ hB)
  rw [inner_sandwich_square,he,← inner_one (sandwich R A),← inner_one (sandwich R B),
    inner_sandwich R A one, inner_sandwich R B one, he,
    real_inner_comm A X,real_inner_comm B X] at hh
  exact hh

end
end CurrentKS.Hermitian

end OAI
