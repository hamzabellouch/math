import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.SquareScalarBound
import OAI.Analysis.MatrixSigning.Matrices.RetractH
import OAI.Analysis.MatrixSigning.Calculus.JetBound

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance : NormedAddCommGroup (Mat d) := inferInstance
private local instance : NormedSpace ℝ (Mat d) := inferInstance
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (Mat d) :=
  (inferInstance : NormedAddCommGroup (Mat d)).toUniformSpace.toTopologicalSpace
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

lemma norm_retractH_le : ‖(retractH (d := d) : Mat d →L[ℝ] H d)‖ ≤ 1 :=
  (hermitianSubmodule d).orthogonalProjectionOnto_norm_le

lemma norm_subtypeH_le : ‖(hermitianSubmodule d).subtypeL‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖v‖ ≤ 1 * ‖v‖
  simp only [one_mul, le_refl]

lemma norm_psd_of_scalar_bound (U : H d) (hU : U ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hUr : U ≤ r • one) : ‖U‖ ≤ r*((d:ℝ)+1) := by
  have ht := realTrace_mono hUr
  rw [realTrace_smul,realTrace_one] at ht
  have hh := inner_nonneg_of_psd U (r • one-U) hU
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUr))
  rw [inner_sub_right,real_inner_smul_right U (one : H d) r,inner_one',real_inner_self_eq_norm_sq] at hh
  have hnt : ‖U‖^2 ≤ r^2*d := by nlinarith [mul_le_mul_of_nonneg_left ht hr]
  have hd : (0:ℝ)≤d := Nat.cast_nonneg d
  have hd' : (d:ℝ)≤(d+1)^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hd' (sq_nonneg r)
  have hn : 0 ≤ r*((d:ℝ)+1) := by positivity
  nlinarith [norm_nonneg U]

lemma invH_norm_of_scalar_lower (U : H d) (hU : U ∈ pd d)
    (hUr : (200:ℝ)⁻¹ • one ≤ U) : ‖invH U‖ ≤ 200*((d:ℝ)+1) := by
  apply norm_psd_of_scalar_bound _ hU.inv.posSemidef (by norm_num : (0:ℝ)≤200)
  have h := inverse_upper_of_lower U hU (by norm_num : (0:ℝ)<200⁻¹) hUr
  simpa only [inv_inv] using h

lemma jetBound_invH_linear (X : E →L[ℝ] H d) (hX : ‖X‖ ≤ 1) {z : E}
    (hz : X z ∈ pd d) {a : ℝ} (ha₁ : 1 ≤ a) (ha : ‖invH (X z)‖ ≤ a) :
    JetBound (fun v => invH (X v)) z (6*a^4) := by
  let Xm := (hermitianSubmodule d).subtypeL.comp X
  have hXm : ‖Xm‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul norm_subtypeH_le hX (norm_nonneg X) zero_le_one)
  have ham : ‖Ring.inverse (Xm z)‖ ≤ a := by
    simp only [Xm,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      ← Matrix.nonsing_inv_eq_ringInverse]
    exact ha
  have hzunit : IsUnit (Xm z) := hz.isUnit
  obtain ⟨h₁,h₂,h₃⟩ := inverse_linear_first_three Xm hXm hzunit ham
  have hc : ContDiffAt ℝ 3 (fun v => Ring.inverse (Xm v)) z :=
    (contDiffAt_inverse_of_unit hzunit).comp z Xm.contDiff.contDiffAt
  have hm : JetBound (fun v => Ring.inverse (Xm v)) z (6*a^4) := by
    have ha0 : 0 ≤ a := le_trans zero_le_one ha₁
    have ha14 : a ≤ a^4 := by simpa only [pow_one] using pow_le_pow_right₀ ha₁ (by norm_num : 1≤4)
    have ha24 : a^2 ≤ a^4 := pow_le_pow_right₀ ha₁ (by norm_num)
    have ha34 : a^3 ≤ a^4 := pow_le_pow_right₀ ha₁ (by norm_num)
    intro n hn
    interval_cases n
    · rw [norm_iteratedFDeriv_zero]; exact ham.trans (by nlinarith [pow_nonneg ha0 4])
    · exact h₁.trans (by nlinarith [pow_nonneg ha0 4])
    · exact h₂.trans (by nlinarith [pow_nonneg ha0 4])
    · exact h₃
  have h := hm.linear_comp (retractH (d := d)) hc norm_retractH_le
  simpa only [Function.comp_def,one_mul,Xm,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,← invH_retract] using h

lemma norm_sandwichCLM_le (A : H d) : ‖(sandwichCLM A : H d →L[ℝ] H d)‖ ≤ ‖A‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro U
  change ‖(A:Mat d)*(U:Mat d)*(A:Mat d)‖ ≤ ‖A‖^2*‖U‖
  calc
    _ ≤ ‖(A:Mat d)‖*‖(U:Mat d)‖*‖(A:Mat d)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by change ‖A‖*‖U‖*‖A‖ = _; ring
end
end CurrentKS.Hermitian

end OAI
