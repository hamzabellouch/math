import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.SandwichCLM

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def jordanCLM (A B : H d) : H d →L[ℝ] H d :=
  sandwichCLM (A+B) - sandwichCLM A - sandwichCLM B

lemma jordanCLM_val (A B U : H d) :
    ((jordanCLM A B U : H d) : Mat d) =
      (A : Mat d) * (U : Mat d) * (B : Mat d) + (B : Mat d) * (U : Mat d) * (A : Mat d) := by
  change ((A : Mat d)+(B : Mat d)) * (U : Mat d) * ((A : Mat d)+(B : Mat d)) -
    (A : Mat d)*(U : Mat d)*(A : Mat d) - (B : Mat d)*(U : Mat d)*(B : Mat d) = _
  noncomm_ring

lemma jordanCLM_symmetric (A B : H d) : (jordanCLM A B).toLinearMap.IsSymmetric := by
  intro U V
  change inner ℝ (sandwich (A+B) U - sandwich A U - sandwich B U) V =
    inner ℝ U (sandwich (A+B) V - sandwich A V - sandwich B V)
  simp only [inner_sub_left, inner_sub_right, inner_sandwich]

lemma jordanCLM_quadratic (A B U : H d) :
    inner ℝ U (jordanCLM A B U) = 2 * inner ℝ B (sandwich U A) := by
  rw [inner_eq_trace, inner_eq_trace, jordanCLM_val, sandwich_val, mul_add, Matrix.trace_add,
    Complex.add_re]
  have h₁ : ((U : Mat d) * ((A : Mat d)*(U : Mat d)*(B : Mat d))).trace =
      ((B : Mat d)* ((U : Mat d)*(A : Mat d)*(U : Mat d))).trace := by
    rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm]
  have h₂ : ((U : Mat d) * ((B : Mat d)*(U : Mat d)*(A : Mat d))).trace =
      ((B : Mat d)* ((U : Mat d)*(A : Mat d)*(U : Mat d))).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [h₁, h₂]
  ring

lemma sandwich_mono (U : H d) {A B : H d} (h : A ≤ B) : sandwich U A ≤ sandwich U B := by
  have hp := sandwich_psd U (B-A) ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h))
  rw [sandwich_sub, mem_psd_iff_nonneg] at hp
  exact sub_nonneg.mp hp

lemma inner_mono_right {P A B : H d} (hP : P ∈ psdCone d) (h : A ≤ B) :
    inner ℝ P A ≤ inner ℝ P B := by
  have hh := inner_nonneg_of_psd P (B-A) hP ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h))
  rw [inner_sub_right] at hh
  linarith

lemma inner_mono_left {P A B : H d} (hP : P ∈ psdCone d) (h : A ≤ B) :
    inner ℝ A P ≤ inner ℝ B P := by
  simpa only [real_inner_comm] using inner_mono_right hP h

lemma trace_square_norm (U : H d) : inner ℝ (Hermitian.one : H d) (sandwich U Hermitian.one) = ‖U‖^2 := by
  rw [inner_eq_trace, sandwich_val, one_val, one_mul, mul_one, ← inner_eq_trace U U]
  exact real_inner_self_eq_norm_sq U

lemma jordanCLM_lower (A B : H d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a • (Hermitian.one : H d) ≤ A) (hB : b • (Hermitian.one : H d) ≤ B) (U : H d) :
    (2*a*b) * ‖U‖^2 ≤ inner ℝ U (jordanCLM A B U) := by
  have hApos : A ∈ psdCone d := (mem_psd_iff_nonneg _).mpr
    ((psd_nonneg (psd_smul (A := (Hermitian.one : H d)) one_mem_psdCone ha)).trans hA)
  have h₁ := inner_mono_left (sandwich_psd U A hApos) hB
  have h₂ := inner_mono_right (P := (Hermitian.one : H d)) one_mem_psdCone (sandwich_mono U hA)
  rw [inner_smul_leftH] at h₁
  rw [sandwich_smul, inner_smul_rightH, trace_square_norm] at h₂
  rw [jordanCLM_quadratic]
  nlinarith [mul_le_mul_of_nonneg_left h₂ hb]

lemma jordanCLM_upper (A B : H d) {a b : ℝ} (hb : 0 ≤ b)
    (hApos : A ∈ psdCone d) (hA : A ≤ a • (Hermitian.one : H d))
    (hB : B ≤ b • (Hermitian.one : H d)) (U : H d) :
    inner ℝ U (jordanCLM A B U) ≤ (2*a*b) * ‖U‖^2 := by
  have h₁ := inner_mono_left (sandwich_psd U A hApos) hB
  have h₂ := inner_mono_right (P := (Hermitian.one : H d)) one_mem_psdCone (sandwich_mono U hA)
  rw [inner_smul_leftH] at h₁
  rw [sandwich_smul, inner_smul_rightH, trace_square_norm] at h₂
  rw [jordanCLM_quadratic]
  nlinarith [mul_le_mul_of_nonneg_left h₂ hb]

end
end CurrentKS.Hermitian

end OAI
