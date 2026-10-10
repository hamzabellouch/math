import Mathlib
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.MatrixLogDet

namespace OAI

/-! Log Hessian Calculus. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma wderiv_inv {f : V n → ℂ} {z : V n}
    (hf : DifferentiableAt ℝ f z) (hn : f z ≠ 0) (a : ℂ) (v : V n) :
    wderiv a v (fun y => (f y)⁻¹) z = -(f z)^(-2 : ℤ)*wderiv a v f z := by
  have h := (hasDerivAt_inv hn).comp_hasFDerivAt z hf.hasFDerivAt
  have he : fderiv ℝ (fun y => (f y)⁻¹) z = -((f z)^2)⁻¹ • fderiv ℝ f z := h.fderiv
  simp only [wderiv,he,_root_.smul_apply,smul_eq_mul]
  simp only [_root_.zpow_neg,zpow_ofNat]
  ring

lemma second_wderiv_log_real {U : Set (V n)} (hU : IsOpen U)
    {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hp : ∀ y ∈ U, f y ≠ 0)
    {z : V n} (hz : z ∈ U) (a b : ℂ) (u v : V n) :
    wderiv b u (wderiv a v (fun y => (Real.log (f y) : ℂ))) z =
      (f z : ℂ)⁻¹*wderiv b u (wderiv a v (fun y => (f y : ℂ))) z -
      (f z : ℂ)^(-2 : ℤ)*wderiv b u (fun y => (f y : ℂ)) z *
        wderiv a v (fun y => (f y : ℂ)) z := by
  have hs := hf.contDiffAt (hU.mem_nhds hz)
  have hc : ContDiffAt ℝ ∞ (fun y => (f y : ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hs
  have he : (wderiv a v (fun y => (Real.log (f y) : ℂ))) =ᶠ[𝓝 z]
      (fun y => (f y : ℂ)⁻¹*wderiv a v (fun y => (f y : ℂ)) y) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact wderiv_log_real (hf.contDiffAt (hU.mem_nhds hy)) (hp y hy) a v
  rw [wderiv_congr he,wderiv_mul
    (show DifferentiableAt ℝ (fun y => (f y : ℂ)⁻¹) z from
      (hc.differentiableAt (by simp)).inv (Complex.ofReal_ne_zero.mpr (hp z hz)))
    ((wderiv_smooth hc a v).differentiableAt (by simp)),
    wderiv_inv (hc.differentiableAt (by simp)) (Complex.ofReal_ne_zero.mpr (hp z hz))]
  ring

lemma dzbar_real_eq_conj {f : V n → ℝ} {z : V n}
    (hf : DifferentiableAt ℝ f z) (v : V n) :
    dzbar v (fun y => (f y : ℂ)) z = star (dz v (fun y => (f y : ℂ)) z) := by
  simp only [dzbar,dz,wderiv,fderiv_ofReal hf]
  apply Complex.ext <;> simp

lemma log_hessian_diagonal {U : Set (V n)} (hU : IsOpen U)
    {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hp : ∀ y ∈ U, f y ≠ 0)
    {z : V n} (hz : z ∈ U) (k : Fin n) :
    (PotentialKaehler.potentialMatrix (fun y => Real.log (f y)) z k k).re =
      (f z)⁻¹*(PotentialKaehler.potentialMatrix f z k k).re -
      (f z)^(-2 : ℤ)*‖dz (e k) (fun y => (f y : ℂ)) z‖^2 := by
  have hs := hf.contDiffAt (hU.mem_nhds hz)
  rw [potentialMatrix_eq_dzbar_dz (hs.log (hp z hz)),
    potentialMatrix_eq_dzbar_dz hs]
  change (wderiv Complex.I (e k) (wderiv (-Complex.I) (e k)
    (fun y => (Real.log (f y) : ℂ))) z).re = _
  rw [second_wderiv_log_real hU hf hp hz]
  change ((f z : ℂ)⁻¹ * dzbar (e k) (dz (e k) (fun y => (f y : ℂ))) z -
    (f z : ℂ)^(-2 : ℤ)*dzbar (e k) (fun y => (f y : ℂ)) z*
      dz (e k) (fun y => (f y : ℂ)) z).re = _
  rw [dzbar_real_eq_conj (hs.differentiableAt (by simp)),mul_assoc,Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.ofReal_inv,← Complex.ofReal_zpow,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,mul_zero,Complex.normSq_eq_norm_sq]
  rfl
end KaehlerCalculus

end
end

end OAI
