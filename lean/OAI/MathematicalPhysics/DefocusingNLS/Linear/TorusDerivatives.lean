import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerTorus
import Mathlib.Analysis.Calculus.SmoothSeries

namespace OAI

/-!
# Coordinate derivatives of the torus Fourier series

For `k>8`, the continuous Fourier Laplacian agrees with the sum of the
ordinary second derivatives along the twelve coordinate circles.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

theorem frequencyCoordinates_coe (n : frequencyLattice) (j : Fin 12) :
    (frequencyCoordinates n j : ℝ) = (n : EuclideanSpace ℝ (Fin 12)) j := by
  simpa [frequencyCoordinates, OrthonormalBasis.coe_toBasis_repr_apply] using
      (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis.restrictScalars_repr_apply ℤ n j

theorem frequencyCoordinates_sq_sum (n : frequencyLattice) :
    ∑ j : Fin 12, (frequencyCoordinates n j : ℝ) ^ 2 = ‖n‖ ^ 2 := by
  simp_rw [frequencyCoordinates_coe]
  exact (EuclideanSpace.real_norm_sq_eq (n : EuclideanSpace ℝ (Fin 12))).symm

theorem frequencyCoordinates_sq_le (n : frequencyLattice) (j : Fin 12) :
    (frequencyCoordinates n j : ℝ) ^ 2 ≤ ‖n‖ ^ 2 := by
  rw [← frequencyCoordinates_sq_sum]
  exact Finset.single_le_sum (f := fun i : Fin 12 => (frequencyCoordinates n i : ℝ) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)

theorem frequencyCoordinates_abs_le (n : frequencyLattice) (j : Fin 12) :
    |(frequencyCoordinates n j : ℝ)| ≤ 1 + ‖n‖ ^ 2 := by
  have h := frequencyCoordinates_sq_le n j
  have hs := sq_nonneg (|(frequencyCoordinates n j : ℝ)| - 1)
  nlinarith [abs_nonneg (frequencyCoordinates n j : ℝ),
    sq_abs (frequencyCoordinates n j : ℝ)]

/-- The real parameter `t` moves along the `j`th coordinate circle. -/
noncomputable def torusCoordinateLine (x : SchrodingerTorus) (j : Fin 12) (t : ℝ) :
    SchrodingerTorus := x + fun l => if l = j then (t : AddCircle (2 * Real.pi)) else 0

@[simp] theorem torusCoordinateLine_zero (x : SchrodingerTorus) (j : Fin 12) :
    torusCoordinateLine x j 0 = x := by
  ext l
  simp [torusCoordinateLine]

theorem torusCharacter_add (n : frequencyLattice) (x y : SchrodingerTorus) :
    torusCharacter n (x + y) = torusCharacter n x * torusCharacter n y := by
  simp only [torusCharacter, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    smul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem torusCharacter_coordinateLine (n : frequencyLattice) (x : SchrodingerTorus)
    (j : Fin 12) (t : ℝ) :
    torusCharacter n (torusCoordinateLine x j t) =
      torusCharacter n x * fourier (frequencyCoordinates n j) (t : AddCircle (2 * Real.pi)) := by
  rw [torusCoordinateLine, torusCharacter_add]
  congr 1
  have hz (m : ℤ) : fourier m (0 : AddCircle (2 * Real.pi)) = 1 := by
    simp [fourier_apply]
  simp only [torusCharacter, ContinuousMap.coe_mk, apply_ite, hz]
  simp

/-- Each torus character has its expected coordinate derivative. -/
theorem hasDerivAt_torusCharacter_coordinateLine (n : frequencyLattice)
    (x : SchrodingerTorus) (j : Fin 12) (t : ℝ) :
    HasDerivAt (fun s => torusCharacter n (torusCoordinateLine x j s))
      (Complex.I * (frequencyCoordinates n j : ℂ) *
        torusCharacter n (torusCoordinateLine x j t)) t := by
  have h := (hasDerivAt_fourier (2 * Real.pi) (frequencyCoordinates n j) t).const_mul
    (torusCharacter n x)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at h
  simpa only [torusCharacter_coordinateLine] using
    h.congr_deriv (by field_simp)

theorem summable_quadratic_sobolev_coefficients (k : ℝ) (hk : 8 < k) (f : FourierL2) :
    Summable (fun n : frequencyLattice => ‖n‖ ^ 2 * ‖sobolevFourierCoefficient k f n‖) := by
  have h := summable_norm_sobolevFourierCoefficient (k - 2) (by linarith)
    (-Complex.I • lowerSobolevGenerator f)
  simpa only [sobolevFourierCoefficient_laplacian, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_pow, abs_norm] using h

theorem summable_derivative_bound (k : ℝ) (hk : 8 < k) (f : FourierL2) :
    Summable (fun n : frequencyLattice => (1 + ‖n‖ ^ 2) *
      ‖sobolevFourierCoefficient k f n‖) := by
  simpa only [add_mul, one_mul] using
    (summable_norm_sobolevFourierCoefficient k (by linarith) f).add
      (summable_quadratic_sobolev_coefficients k hk f)

/-- First coordinate derivative, represented by its absolutely convergent Fourier series. -/
noncomputable def torusPartial (k : ℝ) (f : FourierL2) (j : Fin 12)
    (x : SchrodingerTorus) : ℂ :=
  ∑' n, Complex.I * (frequencyCoordinates n j : ℂ) * sobolevFourierCoefficient k f n *
    torusCharacter n x

/-- Second coordinate derivative, represented by its absolutely convergent Fourier series. -/
noncomputable def torusSecondPartial (k : ℝ) (f : FourierL2) (j : Fin 12)
    (x : SchrodingerTorus) : ℂ :=
  ∑' n, -(frequencyCoordinates n j : ℂ) ^ 2 * sobolevFourierCoefficient k f n *
    torusCharacter n x

lemma torusPartial_term_bound (k : ℝ) (f : FourierL2) (n : frequencyLattice)
    (j : Fin 12) (x : SchrodingerTorus) :
    ‖Complex.I * (frequencyCoordinates n j : ℂ) * sobolevFourierCoefficient k f n *
      torusCharacter n x‖ ≤ (1 + ‖n‖ ^ 2) * ‖sobolevFourierCoefficient k f n‖ := by
  simp only [norm_mul, Complex.norm_I, one_mul, torusCharacter_norm_apply, mul_one,
    Complex.norm_intCast]
  exact mul_le_mul_of_nonneg_right (frequencyCoordinates_abs_le n j) (norm_nonneg _)

lemma torusSecondPartial_term_bound (k : ℝ) (f : FourierL2) (n : frequencyLattice)
    (j : Fin 12) (x : SchrodingerTorus) :
    ‖-(frequencyCoordinates n j : ℂ) ^ 2 * sobolevFourierCoefficient k f n *
      torusCharacter n x‖ ≤ ‖n‖ ^ 2 * ‖sobolevFourierCoefficient k f n‖ := by
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_intCast, sq_abs,
    torusCharacter_norm_apply, mul_one]
  exact mul_le_mul_of_nonneg_right (frequencyCoordinates_sq_le n j) (norm_nonneg _)

/-- Termwise differentiation of the Fourier series gives the actual first coordinate derivative. -/
theorem hasDerivAt_torusFunction_coordinateLine (k : ℝ) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) (j : Fin 12) (t : ℝ) :
    HasDerivAt (fun s => sobolevTorusFunction k f (torusCoordinateLine x j s))
      (torusPartial k f j (torusCoordinateLine x j t)) t := by
  have h := hasDerivAt_tsum (summable_derivative_bound k hk f)
    (y₀ := (0 : ℝ))
    (g := fun n s => sobolevFourierCoefficient k f n *
      torusCharacter n (torusCoordinateLine x j s))
    (g' := fun n s => Complex.I * (frequencyCoordinates n j : ℂ) *
      sobolevFourierCoefficient k f n * torusCharacter n (torusCoordinateLine x j s))
    (fun n s => ((hasDerivAt_torusCharacter_coordinateLine n x j s).const_mul
      (sobolevFourierCoefficient k f n)).congr_deriv (by ring))
    (fun n s => torusPartial_term_bound k f n j _)
    ((summable_norm_sobolevFourierCoefficient k (by linarith) f).of_norm_bounded (by
      intro n
      simp)) t
  convert h using 1
  · funext s
    rw [sobolevTorusFunction_apply k (by linarith)]
    exact (hasSum_sobolevPointEvaluation k (by linarith) _ f).tsum_eq.symm
  · rfl

/-- The derivative of the first coordinate derivative is the stated second series. -/
theorem hasDerivAt_torusPartial_coordinateLine (k : ℝ) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) (j : Fin 12) (t : ℝ) :
    HasDerivAt (fun s => torusPartial k f j (torusCoordinateLine x j s))
      (torusSecondPartial k f j (torusCoordinateLine x j t)) t := by
  have h := hasDerivAt_tsum (summable_quadratic_sobolev_coefficients k hk f)
    (y₀ := (0 : ℝ))
    (g := fun n s => Complex.I * (frequencyCoordinates n j : ℂ) *
      sobolevFourierCoefficient k f n * torusCharacter n (torusCoordinateLine x j s))
    (g' := fun n s => -(frequencyCoordinates n j : ℂ) ^ 2 *
      sobolevFourierCoefficient k f n * torusCharacter n (torusCoordinateLine x j s))
    (fun n s => ((hasDerivAt_torusCharacter_coordinateLine n x j s).const_mul
      (Complex.I * (frequencyCoordinates n j : ℂ) * sobolevFourierCoefficient k f n)).congr_deriv
      (by
        linear_combination (frequencyCoordinates n j : ℂ) ^ 2 *
          sobolevFourierCoefficient k f n * torusCharacter n (torusCoordinateLine x j s) *
          Complex.I_sq))
    (fun n s => torusSecondPartial_term_bound k f n j _)
    ((summable_derivative_bound k hk f).of_norm_bounded (torusPartial_term_bound k f · j _)) t
  exact h

/-- The ordinary coordinate Laplacian equals the continuous spectral Laplacian. -/
theorem sum_torusSecondPartial_eq_laplacian (k : ℝ) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) :
    ∑ j : Fin 12, torusSecondPartial k f j x = torusFourierLaplacian k f x := by
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ =>
    ((summable_quadratic_sobolev_coefficients k hk f).of_norm_bounded
      (torusSecondPartial_term_bound k f · j x)).hasSum)
  have hterms (n : frequencyLattice) :
      ∑ j : Fin 12, -(frequencyCoordinates n j : ℂ) ^ 2 *
        sobolevFourierCoefficient k f n * torusCharacter n x =
      -((‖n‖ ^ 2 : ℝ) : ℂ) * sobolevFourierCoefficient k f n * torusCharacter n x := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib]
    have hn : (∑ j : Fin 12, (frequencyCoordinates n j : ℂ) ^ 2) =
        ((‖n‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast frequencyCoordinates_sq_sum n
    rw [hn]
  simp_rw [hterms] at hsum
  exact hsum.unique (hasSum_torusFourierLaplacian k hk f x)

theorem torusFunction_first_derivative (k : ℝ) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) (j : Fin 12) (t : ℝ) :
    deriv (fun s => sobolevTorusFunction k f (torusCoordinateLine x j s)) t =
      torusPartial k f j (torusCoordinateLine x j t) :=
  (hasDerivAt_torusFunction_coordinateLine k hk f x j t).deriv

theorem torusFunction_second_derivative (k : ℝ) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) (j : Fin 12) (t : ℝ) :
    deriv (deriv (fun s => sobolevTorusFunction k f (torusCoordinateLine x j s))) t =
      torusSecondPartial k f j (torusCoordinateLine x j t) := by
  have h : deriv (fun s => sobolevTorusFunction k f (torusCoordinateLine x j s)) =
      fun s => torusPartial k f j (torusCoordinateLine x j s) :=
    funext (torusFunction_first_derivative k hk f x j)
  rw [h]
  exact (hasDerivAt_torusPartial_coordinateLine k hk f x j t).deriv

/-- The Fourier Laplacian is the sum of the ordinary coordinate second derivatives. -/
theorem sum_coordinate_second_derivative_eq_laplacian (k : ℝ) (hk : 8 < k)
    (f : FourierL2) (x : SchrodingerTorus) :
    ∑ j : Fin 12,
      deriv (deriv (fun s => sobolevTorusFunction k f (torusCoordinateLine x j s))) 0 =
      torusFourierLaplacian k f x := by
  simp_rw [torusFunction_second_derivative k hk, torusCoordinateLine_zero]
  exact sum_torusSecondPartial_eq_laplacian k hk f x

/-- The free evolution solves `i∂ₜu+Δu=0` with the ordinary torus Laplacian. -/
theorem freeTorusEvolution_schrodinger_equation (k : ℝ) (hk : 8 < k)
    (f : FourierL2) (x : SchrodingerTorus) (t : ℝ) :
    Complex.I * deriv (fun s => freeTorusEvolution k f s x) t +
      ∑ j : Fin 12,
        deriv (deriv (fun s => freeTorusEvolution k f t (torusCoordinateLine x j s))) 0 = 0 := by
  change Complex.I * deriv (fun s => freeTorusEvolution k f s x) t +
      ∑ j : Fin 12,
        deriv (deriv (fun s => sobolevTorusFunction k (schrodingerFlow t f)
          (torusCoordinateLine x j s))) 0 = 0
  rw [sum_coordinate_second_derivative_eq_laplacian k hk,
    (hasDerivAt_freeTorusEvolution_point k hk f x t).deriv]
  simp [← mul_assoc]

end DefocusingNLS

end OAI
