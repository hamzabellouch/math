import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.NormRetractH

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance : NormedAddCommGroup (Mat d) := inferInstance
private local instance : NormedSpace ℝ (Mat d) := inferInstance
private local instance : TopologicalSpace (Mat d) :=
  (inferInstance : NormedAddCommGroup (Mat d)).toUniformSpace.toTopologicalSpace

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace


lemma jetBound_inverse_sandwich (X P : E →L[ℝ] H d)
    (hX : ‖X‖ ≤ 1) (hP : ‖P‖ ≤ 1) {z : E} (hz : X z ∈ pd d)
    {a : ℝ} (ha₁ : 1 ≤ a) (ha : ‖invH (X z)‖ ≤ a) (hp : ‖P z‖ ≤ 1) :
    JetBound (fun v => sandwich (invH (X v)) (P v)) z (42*a^5) := by
  let Xm := (hermitianSubmodule d).subtypeL.comp X
  let Pm := (hermitianSubmodule d).subtypeL.comp P
  have hXm : ‖Xm‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul norm_subtypeH_le hX (norm_nonneg X) zero_le_one)
  have hPm : ‖Pm‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul norm_subtypeH_le hP (norm_nonneg P) zero_le_one)
  have ham : ‖Ring.inverse (Xm z)‖ ≤ a := by
    simp only [Xm,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      ← Matrix.nonsing_inv_eq_ringInverse]
    exact ha
  have hpm : ‖Pm z‖ ≤ 1 := hp
  have hzunit : IsUnit (Xm z) := hz.isUnit
  have h₀ : 0 ≤ a := le_trans zero_le_one ha₁
  obtain ⟨h₁,h₂,h₃⟩ := inverse_sandwich_first_three Xm Pm hXm hPm hzunit ha₁ ham hp
  have hi : ContDiffAt ℝ 3 (fun v => Ring.inverse (Xm v)) z :=
    (contDiffAt_inverse_of_unit hzunit).comp z Xm.contDiff.contDiffAt
  let f := fun v => Ring.inverse (Xm v)*Pm v*Ring.inverse (Xm v)
  have hf : ContDiffAt ℝ 3 f z := (hi.mul Pm.contDiff.contDiffAt).mul hi
  have hb : JetBound f z (42*a^5) := by
    have ha25 : a^2 ≤ a^5 := pow_le_pow_right₀ ha₁ (by norm_num)
    have ha35 : a^3 ≤ a^5 := pow_le_pow_right₀ ha₁ (by norm_num)
    have ha45 : a^4 ≤ a^5 := pow_le_pow_right₀ ha₁ (by norm_num)
    have hv : ‖f z‖ ≤ a^2 := by
      calc
        _ ≤ ‖Ring.inverse (Xm z)‖*‖Pm z‖*‖Ring.inverse (Xm z)‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ a*1*a := mul_le_mul (mul_le_mul ham hpm (norm_nonneg _) h₀) ham (norm_nonneg _) (by positivity)
        _ = _ := by ring
    intro n hn
    interval_cases n
    · rw [norm_iteratedFDeriv_zero]; exact hv.trans (by nlinarith [pow_nonneg h₀ 5])
    · exact h₁.trans (by nlinarith [pow_nonneg h₀ 5])
    · exact h₂.trans (by nlinarith [pow_nonneg h₀ 5])
    · exact h₃
  have hh := hb.linear_comp (retractH (d := d)) hf norm_retractH_le
  have he : (retractH (d := d)) ∘ f = fun v => sandwich (invH (X v)) (P v) := by
    funext v
    change retractH (Ring.inverse (Xm v)*Pm v*Ring.inverse (Xm v)) = _
    simp only [Xm,Pm,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      ← Matrix.nonsing_inv_eq_ringInverse]
    exact retractH_coe (sandwich (invH (X v)) (P v))
  rw [he,one_mul] at hh
  exact hh
end
end CurrentKS.Hermitian

end OAI
