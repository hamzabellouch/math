import OAI.Analysis.Mahler.SphereForms
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def normEnergy (n : ℕ) (z : ComplexEuclidean n) : ℂ := (‖z‖ ^ 2 : ℝ)

lemma normEnergy_contDiff (n : ℕ) : ContDiff ℝ 2 (normEnergy n) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_id.norm_sq (𝕜 := ℝ))

/-- The actual d^c of the Euclidean squared norm. -/
lemma dc_normEnergy {n : ℕ} (x v : ComplexEuclidean n) :
    dc (normEnergy n) x v = (-1 / 2 : ℂ) * (inner ℝ x (I • v) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (normEnergy n) _ x at hd
  rw [dc, hd.fderiv]
  simp
  ring

lemma real_inner_complexStructure_swap {n : ℕ} (v w : ComplexEuclidean n) :
    inner ℝ w (I • v) = -inner ℝ v (I • w) := by
  simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

/-- The exterior normalization dd^c |z|^2 is the
standard symplectic two-form, with positive dx_k wedge dy_k orientation. -/
theorem extDeriv_dc_normEnergy {n : ℕ} (x v w : ComplexEuclidean n) :
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v, w] =
      ((∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re) : ℝ) : ℂ) := by
  rw [extDeriv_oneForm (differentiableAt_dcLinear (normEnergy_contDiff n).contDiffAt)]
  have hd (a b : ComplexEuclidean n) :
      fderiv ℝ (fun y => dcLinear (normEnergy n) y a) x b =
        (-1 / 2 : ℂ) * (inner ℝ b (I • a) : ℂ) := by
    have he : (fun y => dcLinear (normEnergy n) y a) =
        (fun y => (-1 / 2 : ℂ) * (inner ℝ (I • a) y : ℂ)) := by
      funext y
      rw [dcLinear_apply, dc_normEnergy, real_inner_comm]
    rw [he]
    have hh := ((Complex.ofRealCLM.comp (innerSL ℝ (I • a))).hasFDerivAt (x := x)).const_mul (-1 / 2 : ℂ)
    change HasFDerivAt (fun y => (-1 / 2 : ℂ) * (inner ℝ (I • a) y : ℂ)) _ x at hh
    rw [hh.fderiv]
    simp [real_inner_comm]
  rw [hd, hd, real_inner_complexStructure_swap v w, Complex.ofReal_neg]
  have he : -(inner ℝ v (I • w)) = ∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re) := by
    simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.inner, Complex.mul_re, Complex.mul_im]
    ring
  rw [← he, Complex.ofReal_neg]
  ring

end Mahler

end OAI
