import Mathlib
import OAI.Geometry.PrescribedPotential.WirtingerConjugate

namespace OAI

/-! Matrix Tensor Calculus. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma mderiv_sub {M N : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (hN : ContDiffAt ℝ ∞ N z) (a : ℂ) (v : V n) :
    mderiv a v (fun y => M y-N y) z = mderiv a v M z-mderiv a v N z := by
  simpa only [sub_eq_add_neg,mderiv_neg hN] using mderiv_add hM hN.neg a v

lemma mderiv_sum {α : Type*} (s : Finset α) {M : α → V n → Matrix (Fin n) (Fin n) ℂ}
    {z : V n} (hM : ∀ i ∈ s, ContDiffAt ℝ ∞ (M i) z) (a : ℂ) (v : V n) :
    mderiv a v (fun y => ∑ i ∈ s, M i y) z = ∑ i ∈ s, mderiv a v (M i) z := by
  ext i j
  simp only [mderiv,Matrix.sum_apply]
  exact wderiv_sum s (fun k hk => (entry_smooth (hM k hk) i j).differentiableAt (by simp)) a v

lemma mderiv_smul {f : V n → ℂ} {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (hM : ContDiffAt ℝ ∞ M z) (a : ℂ) (v : V n) :
    mderiv a v (fun y => f y • M y) z = wderiv a v f z • M z + f z • mderiv a v M z := by
  ext i j
  exact wderiv_mul (hf.differentiableAt (by simp))
    ((entry_smooth hM i j).differentiableAt (by simp)) a v

lemma matrix_smooth_smul {f : V n → ℂ} {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (hM : ContDiffAt ℝ ∞ M z) :
    ContDiffAt ℝ ∞ (fun y => f y • M y) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact hf.mul (entry_smooth hM i j)

lemma mderiv_conjTranspose {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (v : V n) :
    mderiv (-Complex.I) v (fun y => (M y)ᴴ) z = (mderiv Complex.I v M z)ᴴ := by
  ext i j
  exact dz_conj ((entry_smooth hM j i).differentiableAt (by simp)) v

lemma mderiv_bar_conjTranspose {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (v : V n) :
    mderiv Complex.I v (fun y => (M y)ᴴ) z = (mderiv (-Complex.I) v M z)ᴴ := by
  ext i j
  exact dzbar_conj ((entry_smooth hM j i).differentiableAt (by simp)) v

lemma matrix_smooth_conjTranspose {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) : ContDiffAt ℝ ∞ (fun y => (M y)ᴴ) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact Complex.conjCLE.contDiff.contDiffAt.comp z (entry_smooth hM j i)

end KaehlerCalculus

end
end

end OAI
