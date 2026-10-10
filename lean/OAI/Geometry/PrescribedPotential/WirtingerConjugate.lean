import Mathlib
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.MatrixWirtinger

namespace OAI

/-! Wirtinger Conjugate. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma fderiv_conj {f : V n → ℂ} {z : V n} (hf : DifferentiableAt ℝ f z) (v : V n) :
    fderiv ℝ (fun y => star (f y)) z v = star (fderiv ℝ f z v) := by
  exact congrArg (fun T : V n →L[ℝ] ℂ => T v)
    ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z hf.hasFDerivAt).fderiv)

lemma dzbar_conj {f : V n → ℂ} {z : V n} (hf : DifferentiableAt ℝ f z) (v : V n) :
    dzbar v (fun y => star (f y)) z = star (dz v f z) := by
  simp only [dzbar,dz,wderiv,fderiv_conj hf]
  simp

lemma dz_conj {f : V n → ℂ} {z : V n} (hf : DifferentiableAt ℝ f z) (v : V n) :
    dz v (fun y => star (f y)) z = star (dzbar v f z) := by
  simp only [dzbar,dz,wderiv,fderiv_conj hf]
  simp

lemma mderiv_bar_eq_conjTranspose {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hh : ∀ y ∈ U, (M y).IsHermitian) {z : V n} (hz : z ∈ U) (v : V n) :
    mderiv Complex.I v M z = (mderiv (-Complex.I) v M z)ᴴ := by
  ext i j
  have he : (fun y => M y i j) =ᶠ[𝓝 z] (fun y => star (M y j i)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact ((hh y hy).apply i j).symm
  change dzbar v (fun y => M y i j) z = star (dz v (fun y => M y j i) z)
  rw [show dzbar v (fun y => M y i j) z = dzbar v (fun y => star (M y j i)) z
    from wderiv_congr he _ _]
  exact dzbar_conj ((entry_smooth (hM.contDiffAt (hU.mem_nhds hz)) j i).differentiableAt (by simp)) v

lemma closed_dzbar_symmetry {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) (hh : ∀ y ∈ U, (M y).IsHermitian)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    {z : V n} (hz : z ∈ U) (i j k : Fin n) :
    dzbar (e k) (fun y => M y i j) z = dzbar (e i) (fun y => M y k j) z := by
  have h1 := congrFun (congrFun (mderiv_bar_eq_conjTranspose hU hM hh hz (e k)) i) j
  have h2 := congrFun (congrFun (mderiv_bar_eq_conjTranspose hU hM hh hz (e i)) k) j
  change dzbar (e k) (fun y => M y i j) z = star (dz (e k) (fun y => M y j i) z) at h1
  change dzbar (e i) (fun y => M y k j) z = star (dz (e i) (fun y => M y j k) z) at h2
  rw [h1,h2,closed_dz_symmetry hU hM hh hclosed hz j i k]
end KaehlerCalculus

end
end

end OAI
