import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Wirtinger Calculus. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace KaehlerCalculus
variable {n : ℕ}
abbrev V (n : ℕ) := Fin n → ℂ

def wderiv (a : ℂ) (v : V n) (f : V n → ℂ) (z : V n) : ℂ :=
  (fderiv ℝ f z v + a * fderiv ℝ f z (Complex.I • v))/2

def dz (v : V n) (f : V n → ℂ) : V n → ℂ := wderiv (-Complex.I) v f
def dzbar (v : V n) (f : V n → ℂ) : V n → ℂ := wderiv Complex.I v f

lemma wderiv_smooth {f : V n → ℂ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (a : ℂ) (v : V n) :
    ContDiffAt ℝ ∞ (wderiv a v f) z := by
  have hd := hf.fderiv_right (m := ∞) (by simp)
  exact ((hd.clm_apply contDiffAt_const).add
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma wderiv_congr {f g : V n → ℂ} {z : V n} (h : f =ᶠ[𝓝 z] g) (a : ℂ) (v : V n) :
    wderiv a v f z = wderiv a v g z := by
  simp only [wderiv,h.fderiv_eq]

lemma wderiv_add {f g : V n → ℂ} {z : V n}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : ℂ) (v : V n) :
    wderiv a v (fun y => f y+g y) z = wderiv a v f z+wderiv a v g z := by
  simp only [wderiv,fderiv_fun_add hf hg,add_apply]
  ring

lemma wderiv_const_mul {f : V n → ℂ} {z : V n}
    (hf : DifferentiableAt ℝ f z) (a c : ℂ) (v : V n) :
    wderiv a v (fun y => c*f y) z = c*wderiv a v f z := by
  simp only [wderiv,fderiv_const_mul hf,smul_apply,smul_eq_mul]
  ring

lemma wderiv_mul {f g : V n → ℂ} {z : V n}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : ℂ) (v : V n) :
    wderiv a v (fun y => f y*g y) z =
      wderiv a v f z*g z+f z*wderiv a v g z := by
  simp only [wderiv,fderiv_fun_mul hf hg,add_apply,
    smul_apply,smul_eq_mul]
  ring

lemma wderiv_const (a c : ℂ) (v z : V n) : wderiv a v (fun _ => c) z = 0 := by
  simp [wderiv]

lemma fderiv_wderiv {f : V n → ℂ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (a : ℂ) (u v : V n) :
    fderiv ℝ (wderiv a v f) z u =
      (fderiv ℝ (fderiv ℝ f) z u v +
        a*fderiv ℝ (fderiv ℝ f) z u (Complex.I • v))/2 := by
  have hd (w : V n) : DifferentiableAt ℝ (fun y => fderiv ℝ f y w) z :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  unfold wderiv
  simp only [div_eq_mul_inv]
  rw [fderiv_mul_const ((hd v).fun_add ((hd (Complex.I • v)).const_mul a)),
    fderiv_fun_add (hd v) ((hd (Complex.I • v)).const_mul a),fderiv_const_mul (hd (Complex.I • v))]
  simp only [smul_apply,add_apply,smul_eq_mul,
    PotentialKaehler.fderiv_eval_derivative hf]
  ring

lemma wderiv_comm {f : V n → ℂ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (a b : ℂ) (u v : V n) :
    wderiv a u (wderiv b v f) z = wderiv b v (wderiv a u f) z := by
  simp only [wderiv, fderiv_wderiv hf]
  have hs := hf.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top)
  rw [hs u v, hs u (Complex.I • v), hs (Complex.I • u) v,
    hs (Complex.I • u) (Complex.I • v)]
  ring

lemma fderiv_ofReal {f : V n → ℝ} {z : V n}
    (hf : DifferentiableAt ℝ f z) (v : V n) :
    fderiv ℝ (fun y => (f y : ℂ)) z v = (fderiv ℝ f z v : ℂ) := by
  exact congrArg (fun T : V n →L[ℝ] ℂ => T v)
    ((Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv)

lemma snd_fderiv_ofReal {f : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (u v : V n) :
    fderiv ℝ (fderiv ℝ (fun y => (f y : ℂ))) z u v =
      (fderiv ℝ (fderiv ℝ f) z u v : ℂ) := by
  have hc : ContDiffAt ℝ ∞ (fun y => (f y : ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  rw [← PotentialKaehler.fderiv_eval_derivative hc]
  have he : (fun y => fderiv ℝ (fun y => (f y : ℂ)) y v) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ f y v : ℂ)) := by
    filter_upwards [(hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by decide)] with y hy
    exact fderiv_ofReal (hy.differentiableAt (by simp)) v
  rw [he.fderiv_eq, fderiv_ofReal
    (((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)),
    PotentialKaehler.fderiv_eval_derivative hf]

lemma dzbar_dz_real {f : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (u v : V n) :
    dzbar u (dz v (fun y => (f y : ℂ))) z =
      PotentialKaehler.hermitianPart (fderiv ℝ (fderiv ℝ f) z) u v := by
  have hc : ContDiffAt ℝ ∞ (fun y => (f y : ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  simp only [dzbar,dz,wderiv,fderiv_wderiv hc,snd_fderiv_ofReal hf]
  apply Complex.ext <;> simp [PotentialKaehler.hermitianPart] <;> ring

lemma potentialMatrix_eq_dzbar_dz {f : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (i j : Fin n) :
    PotentialKaehler.potentialMatrix f z i j =
      dzbar (Pi.single i 1) (dz (Pi.single j 1) (fun y => (f y : ℂ))) z := by
  rw [dzbar_dz_real hf]
  exact PotentialKaehler.hermitianPartMatrix_apply _ i j
end KaehlerCalculus

end
end

end OAI
