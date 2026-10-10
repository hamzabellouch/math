import Mathlib
import OAI.Geometry.PrescribedPotential.WirtingerCalculus

namespace OAI

/-! Kaehler Closed Derivatives. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
open Anticanonical
variable {n : ℕ}
def e (i : Fin n) : V n := Pi.single i 1

lemma fundamental_e (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ComplexAtlas.fundamentalForm M (e i) (e j) = (M i j).im := by
  simp [ComplexAtlas.fundamentalForm,e]
lemma fundamental_Ie (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ComplexAtlas.fundamentalForm M (Complex.I • e i) (e j) = -(M i j).re := by
  simp [ComplexAtlas.fundamentalForm,e,star_smul,smul_dotProduct]
lemma fundamental_eI (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ComplexAtlas.fundamentalForm M (e i) (Complex.I • e j) = (M i j).re := by
  simp [ComplexAtlas.fundamentalForm,e,Matrix.mulVec_smul,dotProduct_smul]
lemma fundamental_IeI (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ComplexAtlas.fundamentalForm M (Complex.I • e i) (Complex.I • e j) = (M i j).im := by
  simp [ComplexAtlas.fundamentalForm,e,Matrix.mulVec_smul,star_smul,
    smul_dotProduct,dotProduct_smul]

lemma fderiv_re {f : V n → ℂ} {z : V n} (hf : DifferentiableAt ℝ f z) (v : V n) :
    fderiv ℝ (fun y => (f y).re) z v = (fderiv ℝ f z v).re := by
  exact congrArg (fun T : V n →L[ℝ] ℝ => T v)
    ((Complex.reCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv)
lemma fderiv_im {f : V n → ℂ} {z : V n} (hf : DifferentiableAt ℝ f z) (v : V n) :
    fderiv ℝ (fun y => (f y).im) z v = (fderiv ℝ f z v).im := by
  exact congrArg (fun T : V n →L[ℝ] ℝ => T v)
    ((Complex.imCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv)

lemma closed_dz_symmetry {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) (hh : ∀ y ∈ U, (M y).IsHermitian)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    {z : V n} (hz : z ∈ U) (i j k : Fin n) :
    dz (e k) (fun y => M y i j) z = dz (e j) (fun y => M y i k) z := by
  have hd (a b : Fin n) : DifferentiableAt ℝ (fun y => M y a b) z :=
    ((contDiffOn_pi.mp (contDiffOn_pi.mp hM a) b).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hre (a b : Fin n) : (fun y => (M y a b).re) =ᶠ[𝓝 z] (fun y => (M y b a).re) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    simpa only [Complex.star_def,Complex.conj_re] using congrArg Complex.re ((hh y hy).apply b a)
  have him (a b : Fin n) : (fun y => (M y a b).im) =ᶠ[𝓝 z] (fun y => -(M y b a).im) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    have he := congrArg Complex.im ((hh y hy).apply a b)
    simpa only [Complex.star_def,Complex.conj_im] using he.symm
  have hRe (a b : Fin n) (v : V n) :
      (fderiv ℝ (fun y => M y a b) z v).re = (fderiv ℝ (fun y => M y b a) z v).re := by
    rw [← fderiv_re (hd a b), (hre a b).fderiv_eq, fderiv_re (hd b a)]
  have hIm (a b : Fin n) (v : V n) :
      (fderiv ℝ (fun y => M y a b) z v).im = -(fderiv ℝ (fun y => M y b a) z v).im := by
    rw [← fderiv_im (hd a b), (him a b).fderiv_eq, fderiv_fun_neg,
      _root_.neg_apply, fderiv_im (hd b a)]
  have h1 := hclosed z hz (Complex.I • e k) (e i) (e j)
  have h2 := hclosed z hz (Complex.I • e j) (e i) (e k)
  have h3 := hclosed z hz (e k) (e i) (e j)
  have h4 := hclosed z hz (Complex.I • e k) (e i) (Complex.I • e j)
  simp only [fundamental_e,fundamental_Ie,fundamental_eI,fundamental_IeI] at h1 h2 h3 h4
  have hneg (a b : Fin n) : DifferentiableAt ℝ (fun y => (M y a b).re) z :=
    Complex.reCLM.differentiableAt.comp z (hd a b)
  simp only [fderiv_fun_neg,_root_.neg_apply,fderiv_re (hd _ _),fderiv_im (hd _ _)] at h1 h2 h3 h4
  have h5 := hRe j k (e i)
  have h6 := hRe k i (e j)
  have h7 := hRe j i (e k)
  have h8 := hRe k i (Complex.I • e j)
  have h9 := hIm k i (e j)
  apply Complex.ext
  · simp only [dz,wderiv,Complex.div_ofNat_re,Complex.add_re,neg_mul,
      Complex.neg_re,Complex.I_mul_re]
    linarith
  · simp only [dz,wderiv,Complex.div_ofNat_im,Complex.add_im,neg_mul,
      Complex.neg_im,Complex.I_mul_im]
    linarith
end KaehlerCalculus

end
end

end OAI
