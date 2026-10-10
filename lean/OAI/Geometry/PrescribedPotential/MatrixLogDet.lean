import Mathlib
import OAI.Geometry.PrescribedPotential.MatrixWirtinger

namespace OAI

/-! Matrix Log Det. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}
local instance matrixLogDetCS (n : ℕ) : ContinuousSMul ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → Fin n → ℂ))

lemma determinant_smooth : ContDiff ℝ ∞ (Matrix.det : Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  contDiffOn_univ.mp (MatrixSmoothGeneral.determinant contDiffOn_id)

lemma fderiv_det (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.det ≠ 0) :
    fderiv ℝ Matrix.det H K = H.det * (H⁻¹*K).trace := by
  have hd := determinant_smooth.differentiable (by simp) H
  have hl : HasDerivAt (fun t : ℝ => H + t • K) K 0 := by
    convert (hasDerivAt_const (0 : ℝ) H).fun_add
      ((hasDerivAt_id (0 : ℝ)).smul_const K) using 1 <;> first | rfl | simp only [one_smul,zero_add]
  have hdat : HasFDerivAt Matrix.det (fderiv ℝ Matrix.det H) (H + (0:ℝ) • K) := by
    convert hd.hasFDerivAt using 1 <;> first | rfl | simp only [zero_smul,add_zero]
  have h1 := hdat.comp_hasDerivAt 0 hl
  have h2 := (MongeAmpere.hasDerivAt_det_add_smul H K (isUnit_iff_ne_zero.mpr hH)).comp_ofReal
  convert h1.unique h2 using 1

lemma fderiv_det_comp {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (hn : (M z).det ≠ 0) (v : V n) :
    fderiv ℝ (fun y => (M y).det) z v = (M z).det*((M z)⁻¹*fderiv ℝ M z v).trace := by
  have hd := determinant_smooth.differentiable (by simp) (M z)
  rw [fderiv_fun_comp z hd (hM.differentiableAt (by simp)),ContinuousLinearMap.comp_apply]
  exact fderiv_det _ _ hn

lemma fderiv_matrix_apply {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (v : V n) (i j : Fin n) :
    (fderiv ℝ M z v) i j = fderiv ℝ (fun y => M y i j) z v := by
  have hp := (hasFDerivAt_apply j (M z i)).comp z
    ((hasFDerivAt_apply i (M z)).comp z (hM.differentiableAt (by simp)).hasFDerivAt)
  exact (congrArg (fun T : V n →L[ℝ] ℂ => T v) hp.fderiv).symm

lemma mderiv_eq {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (a : ℂ) (v : V n) :
    mderiv a v M z = (1/2:ℂ) • (fderiv ℝ M z v + a • fderiv ℝ M z (Complex.I • v)) := by
  ext i j
  simp only [mderiv,wderiv,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,
    fderiv_matrix_apply hM]
  ring

lemma wderiv_det {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (hn : (M z).det ≠ 0) (a : ℂ) (v : V n) :
    wderiv a v (fun y => (M y).det) z = (M z).det*((M z)⁻¹*mderiv a v M z).trace := by
  rw [mderiv_eq hM]
  simp only [wderiv,fderiv_det_comp hM hn,Matrix.mul_smul,Matrix.mul_add,
    Matrix.trace_smul,Matrix.trace_add,smul_eq_mul]
  ring

lemma wderiv_log_real {f : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (hp : f z ≠ 0) (a : ℂ) (v : V n) :
    wderiv a v (fun y => (Real.log (f y) : ℂ)) z =
      (f z : ℂ)⁻¹*wderiv a v (fun y => (f y : ℂ)) z := by
  have hl := (hf.differentiableAt (by simp)).hasFDerivAt.log hp
  have he (u : V n) : fderiv ℝ (fun y => Real.log (f y)) z u = (f z)⁻¹*fderiv ℝ f z u := by
    rw [hl.fderiv,_root_.smul_apply,smul_eq_mul]
  simp only [wderiv,fderiv_ofReal ((hf.log hp).differentiableAt (by simp)),he,
    fderiv_ofReal (hf.differentiableAt (by simp)),Complex.ofReal_mul,Complex.ofReal_inv]
  ring

lemma wderiv_logdet {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef) {z : V n} (hz : z ∈ U) (a : ℂ) (v : V n) :
    wderiv a v (fun y => (Real.log (M y).det.re : ℂ)) z =
      ((M z)⁻¹*mderiv a v M z).trace := by
  have hs := hM.contDiffAt (hU.mem_nhds hz)
  have hdr : ContDiffAt ℝ ∞ (fun y => (M y).det.re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z (determinant_smooth.contDiffAt.comp z hs)
  have hpos := Complex.pos_iff.mp (hp z hz).det_pos
  rw [wderiv_log_real hdr (ne_of_gt hpos.1)]
  have he : (fun y => ((M y).det.re : ℂ)) =ᶠ[𝓝 z] (fun y => (M y).det) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact Complex.ext (by simp) (by simpa using (Complex.pos_iff.mp (hp y hy).det_pos).2)
  rw [wderiv_congr he,wderiv_det hs (ne_of_gt (hp z hz).det_pos)]
  have hez : ((M z).det.re : ℂ) = (M z).det := he.self_of_nhds
  rw [← hez]
  rw [Complex.ofReal_re,← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos.1)),one_mul]

lemma second_wderiv_logdet {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef) {z : V n} (hz : z ∈ U)
    (a b : ℂ) (u v : V n) :
    wderiv b u (wderiv a v (fun y => (Real.log (M y).det.re : ℂ))) z =
      (-(M z)⁻¹*mderiv b u M z*(M z)⁻¹*mderiv a v M z +
        (M z)⁻¹*mderiv b u (mderiv a v M) z).trace := by
  have hs := hM.contDiffAt (hU.mem_nhds hz)
  have hi := (MatrixSmoothGeneral.inverse hM
    (fun y hy => ne_of_gt (hp y hy).det_pos)).contDiffAt (hU.mem_nhds hz)
  have he : wderiv a v (fun y => (Real.log (M y).det.re : ℂ)) =ᶠ[𝓝 z]
      (fun y => ((M y)⁻¹*mderiv a v M y).trace) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact wderiv_logdet hU hM hp hy a v
  have hprod : ContDiffAt ℝ ∞ (fun y => (M y)⁻¹*mderiv a v M y) z := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ ∞ (fun y => ∑ k, (M y)⁻¹ i k * mderiv a v M y k j) z
    exact ContDiffAt.sum (fun k _ => (entry_smooth hi i k).mul
      (entry_smooth (mderiv_smooth hs a v) k j))
  rw [wderiv_congr he,mderiv_trace hprod,
    mderiv_mul hi (mderiv_smooth hs a v),
    mderiv_inverse hU hM (fun y hy => ne_of_gt (hp y hy).det_pos) hz]

lemma second_wderiv_logdet_at_one {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef) {z : V n} (hz : z ∈ U)
    (hMz : M z = 1) (a b : ℂ) (u v : V n) :
    wderiv b u (wderiv a v (fun y => (Real.log (M y).det.re : ℂ))) z =
      (mderiv b u (mderiv a v M) z).trace - (mderiv b u M z*mderiv a v M z).trace := by
  rw [second_wderiv_logdet hU hM hp hz,hMz]
  simp only [inv_one,neg_mul,one_mul,mul_one,trace_add,trace_neg]
  ring

end KaehlerCalculus

end
end

end OAI
