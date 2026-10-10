import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.Sandwich
import OAI.Analysis.MatrixSigning.Matrices.RealTraceSum

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}
lemma square_shift (X : H d) (a : ℝ) :
    sandwich (X-a • (Hermitian.one : H d)) Hermitian.one =
      sandwich X Hermitian.one-(2*a) • X+a^2 • (Hermitian.one : H d) := by
  apply Subtype.ext
  change ((X : Mat d)-a • 1)*1*((X : Mat d)-a • 1) =
    (X : Mat d)*1*(X : Mat d)-(2*a) • (X : Mat d)+a^2 • 1
  simp only [mul_one,sub_mul,mul_sub,mul_smul_comm,smul_mul_assoc,one_mul]
  module

lemma square_lower (X : H d) {a : ℝ} (ha : 0 ≤ a)
    (hX : a • (Hermitian.one : H d) ≤ X) :
    a^2 • (Hermitian.one : H d) ≤ sandwich X Hermitian.one := by
  have hsq := (mem_psd_iff_nonneg _).mp (sandwich_psd (X-a • (Hermitian.one : H d))
    (Hermitian.one : H d) one_mem_psdCone)
  rw [square_shift] at hsq
  have hlo := smul_order hX (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
  rw [smul_smul] at hlo
  have hh := add_le_add hsq hlo
  have he : sandwich X Hermitian.one-(2*a) • X+a^2 • (Hermitian.one : H d)+(2*a) • X =
      sandwich X Hermitian.one+a^2 • (Hermitian.one : H d) := by abel
  rw [zero_add,he] at hh
  have he' : (2*a*a) • (Hermitian.one : H d) =
      a^2 • (Hermitian.one : H d)+a^2 • (Hermitian.one : H d) := by module
  rw [he'] at hh
  exact (add_le_add_iff_right (a^2 • (Hermitian.one : H d))).mp hh
end
end CurrentKS.Hermitian

end OAI
