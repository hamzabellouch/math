import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffResidualScaling
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace OAI

/-! # The spatial product identity behind the actual cutoff defect -/

open scoped Laplacian ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem second_directional_eq (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (x v : E) :
    iteratedFDeriv ℝ 2 f x ![v, v] =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  rw [iteratedFDeriv_two_apply]
  have h := iteratedFDeriv_clm_apply_const_apply hdf
    (by simp : (1 : ℕ∞ω) ≤ ∞) (x := x) (u := v) (m := fun _ : Fin 1 => v)
  simpa only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h.symm

private theorem second_directional_mul (f g : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v : E) :
    iteratedFDeriv ℝ 2 (fun y => f y * g y) x ![v, v] =
      f x * iteratedFDeriv ℝ 2 g x ![v, v] +
      g x * iteratedFDeriv ℝ 2 f x ![v, v] +
      2 * (fderiv ℝ f x v * fderiv ℝ g x v) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.mp hg).2
  have hfv : Differentiable ℝ (fun y => fderiv ℝ f y v) :=
    hdf.differentiable (by simp) |>.clm_apply (differentiable_const _)
  have hgv : Differentiable ℝ (fun y => fderiv ℝ g y v) :=
    hdg.differentiable (by simp) |>.clm_apply (differentiable_const _)
  have hfg : (fun y => fderiv ℝ (fun z => f z * g z) y v) =
      fun y => f y * fderiv ℝ g y v + g y * fderiv ℝ f y v := by
    funext y
    rw [fderiv_fun_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have h₁ : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y v) x :=
    (hf.differentiable (by simp) x).mul (hgv x)
  have h₂ : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y v) x :=
    (hg.differentiable (by simp) x).mul (hfv x)
  rw [second_directional_eq _ (hf.mul hg), hfg,
    fderiv_fun_add h₁ h₂,
    fderiv_fun_mul (hf.differentiable (by simp) x) (hgv x),
    fderiv_fun_mul (hg.differentiable (by simp) x) (hfv x),
    second_directional_eq f hf, second_directional_eq g hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem laplacian_complex_mul (f g : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    Δ (fun y => f y * g y) x = f x * Δ g x + g x * Δ f x +
      2 * ∑ j : Fin 12, fderiv ℝ f x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) *
        fderiv ℝ g x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ)]
  simp_rw [second_directional_mul f g hf hg]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem laplacian_complex_real_mul (χ : E → ℝ) (Q : E → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hQ : ContDiff ℝ ∞ Q) (x : E) :
    Δ (fun y => (χ y : ℂ) * Q y) x = (χ x : ℂ) * Δ Q x +
      (Δ χ x : ℂ) * Q x + 2 * ∑ j : Fin 12,
        (fderiv ℝ χ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
          fderiv ℝ Q x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) := by
  have hc : ContDiff ℝ ∞ (fun y => (χ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hl : Δ (fun y => (χ y : ℂ)) x = (Δ χ x : ℂ) :=
    (hχ.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left (l := Complex.ofRealCLM)
  have hd (v : E) : fderiv ℝ (fun y => (χ y : ℂ)) x v = (fderiv ℝ χ x v : ℂ) := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x (hχ.differentiable (by simp) x).hasFDerivAt
    exact congrArg (fun A : E →L[ℝ] ℂ => A v) h.fderiv
  rw [laplacian_complex_mul _ Q hc hQ, hl]
  simp_rw [hd]
  ring

theorem laplacian_real_dilation (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (r : ℝ) (x : E) :
    Δ (fun y => χ (r • y)) x = r ^ (2 : ℕ) * Δ χ (r • x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ)]
  have hd : iteratedFDeriv ℝ 2 (fun y => χ (r • y)) x =
      r ^ (2 : ℕ) • iteratedFDeriv ℝ 2 χ (r • x) := by
    simpa only using! congrFun (iteratedFDeriv_comp_const_smul r
      (hχ.of_le (by simp : (2 : ℕ∞ω) ≤ ∞))) x
  rw [hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_apply, smul_eq_mul]

theorem fderiv_real_dilation (χ : E → ℝ) (_hχ : Differentiable ℝ χ)
    (r : ℝ) (x v : E) :
    fderiv ℝ (fun y => χ (r • y)) x v = r * fderiv ℝ χ (r • x) v := by
  rw [fderiv_comp_smul]
  simp only [smul_apply, smul_eq_mul]

theorem cutoffResidual_spatial_identity (m : ℕ) (L : ℝ) (χ : E → ℝ) (Q : E → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hQ : ContDiff ℝ ∞ Q) (y : E) :
    Δ (fun z => (χ (L⁻¹ • z) : ℂ) * Q z) y -
        oddPowerNonlinearity m ((χ (L⁻¹ • y) : ℂ) * Q y) =
      (χ (L⁻¹ • y) : ℂ) * (Δ Q y - oddPowerNonlinearity m (Q y)) +
        cutoffResidual m L χ Q y := by
  have hc : ContDiff ℝ ∞ (fun z : E => χ (L⁻¹ • z)) :=
    hχ.comp (contDiff_id.const_smul L⁻¹)
  rw [laplacian_complex_real_mul (fun z : E => χ (L⁻¹ • z)) Q hc hQ,
    laplacian_real_dilation χ hχ, oddPowerNonlinearity_real_mul]
  simp_rw [fderiv_real_dilation χ (hχ.differentiable (by simp)), Complex.ofReal_mul]
  have hsum : (∑ j : Fin 12, ((L⁻¹ : ℝ) : ℂ) *
      (fderiv ℝ χ (L⁻¹ • y) ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
        fderiv ℝ Q y ((EuclideanSpace.basisFun (Fin 12) ℝ) j)) =
      ((L⁻¹ : ℝ) : ℂ) * ∑ j : Fin 12,
        (fderiv ℝ χ (L⁻¹ • y) ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
          fderiv ℝ Q y ((EuclideanSpace.basisFun (Fin 12) ℝ) j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  unfold cutoffResidual
  push_cast
  ring

end DefocusingNLS

end OAI
