import Mathlib
import OAI.Geometry.PrescribedPotential.WirtingerConjugate

namespace OAI

/-! Scalar Product Laplacian. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def holGradient (f : V n → ℝ) (z : V n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun k => dz (e k) (fun y => (f y:ℂ)) z)

def holGradientSquare (f : V n → ℝ) (z : V n) : ℝ := ‖holGradient f z‖^2

def gradientCross (f g : V n → ℝ) (z : V n) : ℝ :=
  2*(inner ℂ (holGradient f z) (holGradient g z)).re

lemma holGradientSquare_eq (f : V n → ℝ) (z : V n) :
    holGradientSquare f z = ∑ k, ‖dz (e k) (fun y => (f y:ℂ)) z‖^2 := by
  rw [holGradientSquare,PiLp.norm_sq_eq_of_L2]
  rfl

lemma gradientCross_sq (f g : V n → ℝ) (z : V n) :
    (gradientCross f g z)^2 ≤ 4*holGradientSquare f z*holGradientSquare g z := by
  have hi := norm_inner_le_norm (𝕜 := ℂ) (holGradient f z) (holGradient g z)
  have hr := Complex.abs_re_le_norm (inner ℂ (holGradient f z) (holGradient g z))
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (hr.trans hi)
  simp only [sq_abs,mul_pow] at hs
  unfold gradientCross holGradientSquare
  nlinarith

lemma dzbar_real {f : V n → ℝ} {z : V n} (hf : ContDiffAt ℝ ∞ f z) (v : V n) :
    dzbar v (fun y => (f y:ℂ)) z = star (dz v (fun y => (f y:ℂ)) z) := by
  have hd : DifferentiableAt ℝ (fun y => (f y:ℂ)) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hf).differentiableAt (by simp)
  have hh := dzbar_conj hd v
  simpa only [Complex.star_def,Complex.conj_ofReal] using hh

lemma potentialMatrix_trace_mul {f g : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    (PotentialKaehler.potentialMatrix (fun y => f y*g y) z).trace.re =
      f z*(PotentialKaehler.potentialMatrix g z).trace.re +
      g z*(PotentialKaehler.potentialMatrix f z).trace.re + gradientCross f g z := by
  have hfc : ContDiffAt ℝ ∞ (fun y => (f y:ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have hgc : ContDiffAt ℝ ∞ (fun y => (g y:ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hg
  have hd (k : Fin n) : dz (e k) (fun y => ((f y*g y:ℝ):ℂ)) =ᶠ[𝓝 z]
      (fun y => dz (e k) (fun x => (f x:ℂ)) y*(g y:ℂ)+(f y:ℂ)*dz (e k) (fun x => (g x:ℂ)) y) := by
    filter_upwards [(hfc.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp),
      (hgc.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)] with y hyF hyG
    simp only [Complex.ofReal_mul]
    exact wderiv_mul (hyF.differentiableAt (by simp)) (hyG.differentiableAt (by simp)) _ _
  have hdd (k : Fin n) : (PotentialKaehler.potentialMatrix (fun y => f y*g y) z) k k =
      (g z:ℂ)*(PotentialKaehler.potentialMatrix f z) k k +
      (f z:ℂ)*(PotentialKaehler.potentialMatrix g z) k k +
      dz (e k) (fun y => (f y:ℂ)) z*star (dz (e k) (fun y => (g y:ℂ)) z)+
      star (dz (e k) (fun y => (f y:ℂ)) z)*dz (e k) (fun y => (g y:ℂ)) z := by
    rw [potentialMatrix_eq_dzbar_dz (hf.mul hg)]
    change wderiv Complex.I (e k) (dz (e k) _) z = _
    rw [wderiv_congr (hd k)]
    unfold dz
    rw [wderiv_add
      (((wderiv_smooth hfc (-Complex.I) (e k)).mul hgc).differentiableAt (by simp))
      ((hfc.mul (wderiv_smooth hgc (-Complex.I) (e k))).differentiableAt (by simp)),
      wderiv_mul ((wderiv_smooth hfc (-Complex.I) (e k)).differentiableAt (by simp)) (hgc.differentiableAt (by simp)),
      wderiv_mul (hfc.differentiableAt (by simp)) ((wderiv_smooth hgc (-Complex.I) (e k)).differentiableAt (by simp))]
    change dzbar (e k) (dz (e k) _) z * _ + dz (e k) _ z * dzbar (e k) _ z +
      (dzbar (e k) _ z * dz (e k) _ z + _ * dzbar (e k) (dz (e k) _) z) = _
    have hef : dzbar (e k) (dz (e k) (fun y => (f y:ℂ))) z = PotentialKaehler.potentialMatrix f z k k :=
      (potentialMatrix_eq_dzbar_dz hf k k).symm
    have heg : dzbar (e k) (dz (e k) (fun y => (g y:ℂ))) z = PotentialKaehler.potentialMatrix g z k k :=
      (potentialMatrix_eq_dzbar_dz hg k k).symm
    rw [dzbar_real hf,dzbar_real hg,hef,heg]
    change _ = (g z:ℂ)*_ + (f z:ℂ)*_ + dz (e k) _ z*star (dz (e k) _ z) + star (dz (e k) _ z)*dz (e k) _ z
    ring
  simp only [Matrix.trace,Matrix.diag_apply,hdd,Complex.re_sum,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Finset.sum_add_distrib,← Finset.mul_sum,gradientCross,holGradient,
    PiLp.inner_apply,RCLike.inner_apply,Complex.star_def]
  simp only [Complex.conj_re,Complex.conj_im]
  simp only [mul_comm]
  ring_nf
end KaehlerCalculus

end
end

end OAI
