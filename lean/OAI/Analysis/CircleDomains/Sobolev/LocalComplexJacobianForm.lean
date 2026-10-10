import OAI.Analysis.CircleDomains.Sobolev.SmoothDiskGreen

namespace OAI

/-! Local smooth Jacobian one-forms, on the actual open set where a map
is smooth. Their curl is the determinant of its real differential. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma smooth_complex_partial_commute_at {v : ℂ → ℝ} {z : ℂ}
    (hv : ContDiffAt ℝ (⊤ : ℕ∞) v z) (p q : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ v w q) z p =
      fderiv ℝ (fun w => fderiv ℝ v w p) z q := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    ((hv.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num))
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact hv.isSymmSndFDerivAt (by simp) _ _

lemma smooth_complex_partial_on {v : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v O) (p : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ v z p) O := by
  intro z hz
  exact (((hv.contDiffAt (hO.mem_nhds hz)).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    contDiffAt_const).contDiffWithinAt

lemma smooth_complex_jacobian_curl {a b : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a O)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b O) {z : ℂ} (hz : z ∈ O) :
    fderiv ℝ (fun z => a z * fderiv ℝ b z Complex.I) z 1 -
        fderiv ℝ (fun z => a z * fderiv ℝ b z 1) z Complex.I =
      fderiv ℝ a z 1 * fderiv ℝ b z Complex.I -
        fderiv ℝ a z Complex.I * fderiv ℝ b z 1 := by
  have had := (ha.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hbd (p : ℂ) := ((smooth_complex_partial_on hO hb p).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  rw [fderiv_fun_mul had (hbd Complex.I), fderiv_fun_mul had (hbd 1)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [smooth_complex_partial_commute_at (hb.contDiffAt (hO.mem_nhds hz)) 1 Complex.I]
  ring

lemma holomorphic_real_jacobian {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) :
    fderiv ℝ (fun w => (F w).re) z 1 * fderiv ℝ (fun w => (F w).im) z Complex.I -
        fderiv ℝ (fun w => (F w).re) z Complex.I * fderiv ℝ (fun w => (F w).im) z 1 =
      ‖deriv F z‖^2 := by
  have hd := hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hre := (Complex.reCLM.hasFDerivAt.comp z hd).fderiv
  have him := (Complex.imCLM.hasFDerivAt.comp z hd).fderiv
  change fderiv ℝ (Complex.reCLM ∘ F) z 1 * fderiv ℝ (Complex.imCLM ∘ F) z Complex.I -
    fderiv ℝ (Complex.reCLM ∘ F) z Complex.I * fderiv ℝ (Complex.imCLM ∘ F) z 1 = _
  rw [hre, him]
  change (1 * deriv F z).re * (Complex.I * deriv F z).im -
    (Complex.I * deriv F z).re * (1 * deriv F z).im = _
  simp only [one_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, zero_sub, Complex.sq_norm, Complex.normSq_apply]
  ring

end CircleDomainRigidity

end

end OAI
