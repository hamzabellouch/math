import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section

noncomputable section
namespace SKGap.LogDet
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def detMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by change Continuous (fun M : Matrix ι ι ℝ => M.det); fun_prop }

lemma hasDerivAt_det_update {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) :
    HasDerivAt (fun x => (Q x).det) (∑ i, ((Q t).updateRow i (Q' i)).det) t := by
  have hrow (i : ι) : HasDerivAt (fun x => Q x i) (Q' i) t := hasDerivAt_pi.mpr (hQ i)
  have h := (HasFDerivAt.multilinear_comp (f := detMultilinear (ι := ι))
    (fun i => (hrow i).hasFDerivAt)).hasDerivAt
  convert h using 1 <;> try rfl
  simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]
  rfl

lemma det_updateRow_trace (M H : Matrix ι ι ℝ) :
    (∑ i, (M.updateRow i (H i)).det)= (H*M.adjugate).trace := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.cramer_transpose_apply,Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma hasDerivAt_det_adjugate {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) :
    HasDerivAt (fun x => (Q x).det) (Q'*(Q t).adjugate).trace t := by
  simpa only [det_updateRow_trace] using hasDerivAt_det_update hQ

lemma adjugate_eq_det_smul_inv (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    M.adjugate=M.det • M⁻¹ := by
  have hd : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp hM |>.ne_zero
  rw [Matrix.inv_def,Ring.inverse_eq_inv,smul_smul,mul_inv_cancel₀ hd,one_smul]

lemma hasDerivAt_det {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) (hunit : IsUnit (Q t)) :
    HasDerivAt (fun x => (Q x).det) ((Q t).det*(Q'*(Q t)⁻¹).trace) t := by
  have h := hasDerivAt_det_adjugate hQ
  rw [adjugate_eq_det_smul_inv _ hunit,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul] at h
  exact h

lemma hasDerivAt_logdet {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) (hunit : IsUnit (Q t)) :
    HasDerivAt (fun x => Real.log (Q x).det) (Q'*(Q t)⁻¹).trace t := by
  have hd : (Q t).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero
  have h := (hasDerivAt_det hQ hunit).log hd
  convert h using 1
  field_simp
end SKGap.LogDet
end
end

end OAI
