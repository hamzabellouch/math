import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianCalculus
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace OAI

/-! # Cartesian calculus for a radial test times a spherical harmonic

The degree-zero extension of the spherical harmonic is kept explicit:
its Euler derivative is zero and its Cartesian Laplacian is the spherical
eigenvalue divided by the squared radius. All formulas are local away from zero.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem second_directional_complex_mul_at (f g : E → ℂ) (x v : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedFDeriv ℝ 2 (fun y => f y * g y) x ![v, v] =
      f x * iteratedFDeriv ℝ 2 g x ![v, v] +
      g x * iteratedFDeriv ℝ 2 f x ![v, v] +
      2 * (fderiv ℝ f x v * fderiv ℝ g x v) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hfv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    hdf.clm_apply (differentiableAt_const v)
  have hgv : DifferentiableAt ℝ (fun y => fderiv ℝ g y v) x :=
    hdg.clm_apply (differentiableAt_const v)
  have hfg : (fun y => fderiv ℝ (fun z => f z * g z) y v) =ᶠ[𝓝 x]
      (fun y => f y * fderiv ℝ g y v + g y * fderiv ℝ f y v) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    rw [fderiv_fun_mul (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have h₁ : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y v) x :=
    (hf.differentiableAt (by norm_num)).mul hgv
  have h₂ : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y v) x :=
    (hg.differentiableAt (by norm_num)).mul hfv
  rw [radial_second_directional_eq _ x v (hf.mul hg), hfg.fderiv_eq,
    fderiv_fun_add h₁ h₂,
    fderiv_fun_mul (hf.differentiableAt (by norm_num)) hgv,
    fderiv_fun_mul (hg.differentiableAt (by norm_num)) hfv,
    radial_second_directional_eq f x v hf, radial_second_directional_eq g x v hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem laplacian_complex_mul_at (f g : E → ℂ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y => f y * g y) x = f x * Δ g x + g x * Δ f x +
      2 * ∑ j : Fin 12, fderiv ℝ f x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) *
        fderiv ℝ g x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ)]
  simp_rw [second_directional_complex_mul_at f g x _ hf hg]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem radial_basis_derivative_contraction (Y : E → ℂ) (x : E) :
    (∑ j : Fin 12, (inner ℝ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
      fderiv ℝ Y x ((EuclideanSpace.basisFun (Fin 12) ℝ) j)) = fderiv ℝ Y x x := by
  have he := congrArg (fderiv ℝ Y x) ((EuclideanSpace.basisFun (Fin 12) ℝ).sum_repr' x)
  simpa only [map_sum, map_smul, Complex.real_smul, real_inner_comm] using he

/-- The dilation derivative of the same test contains no angular term. -/
theorem radialSquare_harmonic_test_euler (q : ℝ → ℂ) (Y : E → ℂ)
    (x : E) (hq : DifferentiableAt ℝ q (‖x‖ ^ 2))
    (hY : DifferentiableAt ℝ Y x) (hEuler : fderiv ℝ Y x x = 0) :
    fderiv ℝ (fun y : E => q (‖y‖ ^ 2) * Y y) x x =
      ((2 * ‖x‖ ^ 2 : ℝ) : ℂ) * deriv q (‖x‖ ^ 2) * Y x := by
  have hr : DifferentiableAt ℝ (fun y : E => q (‖y‖ ^ 2)) x :=
    hq.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt
  rw [fderiv_fun_mul hr hY]
  simp only [add_apply, smul_apply, smul_eq_mul, hEuler, mul_zero, zero_add]
  rw [radialSquareLift_fderiv q x x hq, real_inner_self_eq_norm_sq]
  ring

/-- The Laplacian of a squared-radius test times a degree-zero harmonic
extension. Here λ is the spherical eigenvalue ell(ell+10). -/
theorem radialSquare_harmonic_test_laplacian (q : ℝ → ℂ) (Y : E → ℂ)
    (x : E) (lam : ℂ) (hq : ContDiffAt ℝ 2 q (‖x‖ ^ 2))
    (hY : ContDiffAt ℝ 2 Y x) (hEuler : fderiv ℝ Y x x = 0)
    (hEigen : Δ Y x = -(lam / (‖x‖ ^ 2 : ℝ)) * Y x) :
    Δ (fun y : E => q (‖y‖ ^ 2) * Y y) x =
      (((4 * ‖x‖ ^ 2 : ℝ) : ℂ) * deriv (deriv q) (‖x‖ ^ 2) +
        24 * deriv q (‖x‖ ^ 2) - lam / (‖x‖ ^ 2 : ℝ) * q (‖x‖ ^ 2)) * Y x := by
  have hr : ContDiffAt ℝ 2 (fun y : E => q (‖y‖ ^ 2)) x :=
    hq.comp x (contDiff_norm_sq ℝ).contDiffAt
  rw [laplacian_complex_mul_at _ Y x hr hY, radialSquareLift_laplacian q x hq, hEigen]
  simp_rw [radialSquareLift_fderiv q x _ (hq.differentiableAt (by norm_num))]
  have hs : (∑ j : Fin 12,
      (((2 * inner ℝ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℝ) : ℂ) *
        deriv q (‖x‖ ^ 2)) * fderiv ℝ Y x ((EuclideanSpace.basisFun (Fin 12) ℝ) j)) = 0 := by
    calc
      _ = (2 * deriv q (‖x‖ ^ 2)) * ∑ j : Fin 12,
          (inner ℝ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
            fderiv ℝ Y x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        ring
      _ = 0 := by rw [radial_basis_derivative_contraction, hEuler, mul_zero]
  rw [hs]
  ring

/-- Constancy on positive rays gives the zero Euler derivative used above. -/
theorem zero_euler_of_ray_constant (Y : E → ℂ) (x : E)
    (hY : DifferentiableAt ℝ Y x)
    (hRay : ∀ t : ℝ, 0 < t → Y (t • x) = Y x) : fderiv ℝ Y x x = 0 := by
  have hline : HasDerivAt (fun t : ℝ => Y (t • x)) (fderiv ℝ Y x x) 1 := by
    have hy : HasFDerivAt Y (fderiv ℝ Y x) ((1 : ℝ) • x) := by
      simpa only [one_smul] using hY.hasFDerivAt
    simpa only [Function.comp_def, id_eq, one_smul] using hy.comp_hasDerivAt (1 : ℝ)
      ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have he : (fun t : ℝ => Y (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun _ => Y x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hRay t ht
  exact hline.unique ((hasDerivAt_const (1 : ℝ) (Y x)).congr_of_eventuallyEq he)

end DefocusingNLS

end OAI
