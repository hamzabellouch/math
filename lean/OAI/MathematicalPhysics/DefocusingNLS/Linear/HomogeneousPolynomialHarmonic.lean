import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolynomialCalculus
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialPowerCalculus
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSphereHarmonicSpan

namespace OAI

/-! # Degree-zero extensions of homogeneous harmonic polynomials

The ambient Laplacian of the extension is the spherical eigenvalue
`-ell * (ell + 10) / r²`. This supplies actual angular tests rather than an
assumed complete family of spherical harmonics.
-/

open Set MvPolynomial
open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def physicalHarmonicExtension (p : PhysicalRealPolynomial) (ell : ℕ)
    (x : E) : ℂ :=
  physicalRadiusPower (-(ell : ℝ) / 2) x * physicalPolynomialFunction p x

theorem physicalRadiusPower_neg_nat_half (ell : ℕ) (x : E) :
    physicalRadiusPower (-(ell : ℝ) / 2) x = ((‖x‖ : ℂ) ^ ell)⁻¹ := by
  have he : (2 : ℝ) * (-(ell : ℝ) / 2) = -(ell : ℝ) := by ring
  unfold physicalRadiusPower
  rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.rpow_neg (norm_nonneg x), Real.rpow_natCast]
  simp only [Complex.ofReal_inv, Complex.ofReal_pow]

theorem physicalHarmonicExtension_eq_div (p : PhysicalRealPolynomial) (ell : ℕ) (x : E) :
    physicalHarmonicExtension p ell x =
      physicalPolynomialFunction p x / (‖x‖ : ℂ) ^ ell := by
  rw [physicalHarmonicExtension, physicalRadiusPower_neg_nat_half]
  ring

theorem physicalHarmonicExtension_contDiffAt (p : PhysicalRealPolynomial) (ell : ℕ)
    (x : E) (hx : x ≠ 0) : ContDiffAt ℝ ∞ (physicalHarmonicExtension p ell) x :=
  (physicalRadiusPower_contDiffAt _ x hx).mul
    (physicalPolynomialFunction_contDiff p).contDiffAt

theorem physicalHarmonicExtension_ray (p : PhysicalRealPolynomial) (ell : ℕ)
    (hp : p.IsHomogeneous ell) (x : E) (t : ℝ) (ht : 0 < t) :
    physicalHarmonicExtension p ell (t • x) = physicalHarmonicExtension p ell x := by
  rw [physicalHarmonicExtension_eq_div, physicalHarmonicExtension_eq_div,
    physicalPolynomialFunction_smul p ell hp, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    Complex.ofReal_mul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero ell (Complex.ofReal_ne_zero.mpr ht.ne'))

theorem physicalHarmonicExtension_sphere (p : PhysicalRealPolynomial) (ell : ℕ)
    (z : PhysicalUnitSphere) :
    physicalHarmonicExtension p ell z.1 = (physicalSpherePolynomial p z : ℂ) := by
  have hz : ‖z.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  rw [physicalHarmonicExtension_eq_div, hz, Complex.ofReal_one, one_pow, div_one,
    physicalPolynomialFunction_eval, physicalSpherePolynomial_apply]

theorem physicalHarmonicExtension_laplacian (p : PhysicalRealPolynomial) (ell : ℕ)
    (hp : p.IsHomogeneous ell) (hDp : physicalPolynomialLaplacian p = 0)
    (x : E) (hx : x ≠ 0) :
    Δ (physicalHarmonicExtension p ell) x =
      -(((ell : ℂ) * (ell + 10)) / (‖x‖ ^ 2 : ℝ)) * physicalHarmonicExtension p ell x := by
  let c : ℝ := -(ell : ℝ) / 2
  have hs : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hP : ContDiffAt ℝ 2 (physicalPolynomialFunction p) x :=
    ((physicalPolynomialFunction_contDiff p).of_le (by simp)).contDiffAt
  have hR : ContDiffAt ℝ 2 (physicalRadiusPower c) x :=
    (physicalRadiusPower_contDiffAt c x hx).of_le (by simp)
  have hsum : (∑ i : Fin 12,
      fderiv ℝ (physicalRadiusPower c) x (EuclideanSpace.basisFun (Fin 12) ℝ i) *
        fderiv ℝ (physicalPolynomialFunction p) x (EuclideanSpace.basisFun (Fin 12) ℝ i)) =
      (2 * (c : ℂ) / (‖x‖ ^ 2 : ℝ) * physicalRadiusPower c x) *
        fderiv ℝ (physicalPolynomialFunction p) x x := by
    rw [← radial_basis_derivative_contraction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [physicalRadiusPower_fderiv c x _ hx]
    ring
  change Δ (fun y => physicalRadiusPower c y * physicalPolynomialFunction p y) x = _
  rw [laplacian_complex_mul_at _ _ x hR hP, physicalPolynomialFunction_laplacian, hDp,
    map_zero, Pi.zero_apply, mul_zero, zero_add, physicalRadiusPower_laplacian c x hx,
    hsum, physicalPolynomialFunction_euler p ell hp]
  dsimp only [physicalHarmonicExtension, c]
  push_cast
  field_simp [hs]
  ring

end DefocusingNLS

end OAI
