import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyInterpolation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierDerivatives

namespace OAI

/-! # Ordered Cartesian derivatives and the high homogeneous energy

The sum over all ordered k-tuples of Cartesian directions is exactly the
Fourier weight |ξ|^(2k). This supplies the high-energy interpretation needed
to apply one pointwise principal potential to each derivative component.
-/

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousOrderedDerivative (N : ℕ) (j : Fin N → Fin 12)
    (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  ∂^{fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i)} f

private theorem radianFourierKernel_iteratedLineDeriv (N : ℕ) (v : Fin N → E)
    (f : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (∂^{v} f) ξ =
      (∏ i, ((inner ℝ ξ (v i) : ℂ) * Complex.I)) * radianFourierKernel f ξ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [iteratedLineDerivOp_succ_left, radianFourierKernel_lineDeriv, ih,
        Fin.prod_univ_succ]
      simp only [Fin.tail_def]
      ring

theorem homogeneousOrderedDerivative_fourier (N : ℕ) (j : Fin N → Fin 12)
    (f : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (homogeneousOrderedDerivative N j f) ξ =
      (∏ i, ((ξ (j i) : ℂ) * Complex.I)) * radianFourierKernel f ξ := by
  simpa only [homogeneousOrderedDerivative, EuclideanSpace.inner_basisFun_real] using
    radianFourierKernel_iteratedLineDeriv N
      (fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i)) f ξ

theorem homogeneousOrderedDerivative_fourier_sum (N : ℕ) (f : 𝓢(E, ℂ)) (ξ : E) :
    (∑ j : Fin N → Fin 12, ‖radianFourierKernel (homogeneousOrderedDerivative N j f) ξ‖ ^ 2) =
      ‖ξ‖ ^ (2 * N) * ‖radianFourierKernel f ξ‖ ^ 2 := by
  have hterm (j : Fin N → Fin 12) :
      ‖radianFourierKernel (homogeneousOrderedDerivative N j f) ξ‖ ^ 2 =
        (∏ i, (ξ (j i)) ^ 2) * ‖radianFourierKernel f ξ‖ ^ 2 := by
    rw [homogeneousOrderedDerivative_fourier, norm_mul, mul_pow]
    rw [norm_prod, ← Finset.prod_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _hi
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, sq_abs]
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  congr 1
  rw [← Fintype.sum_pow (fun i : Fin 12 => (ξ i) ^ 2) N]
  rw [← EuclideanSpace.real_norm_sq_eq, pow_mul]

private theorem integrable_schwartz_norm_sq (f : 𝓢(E, ℂ)) :
    Integrable (fun x => ‖f x‖ ^ 2) :=
  (f.memLp 2).integrable_norm_pow (p := 2) (by norm_num)

theorem homogeneousOrderedDerivative_energy (N : ℕ) (f : 𝓢(E, ℂ)) :
    (∑ j : Fin N → Fin 12, ∫ x : E, ‖homogeneousOrderedDerivative N j f x‖ ^ 2) =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        homogeneousFrequencyEnergy (N : ℝ) (radianFourierKernel f) := by
  have hzero (j : Fin N → Fin 12) :
      (∫ x : E, ‖homogeneousOrderedDerivative N j f x‖ ^ 2) =
        ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
          homogeneousFrequencyEnergy 0 (radianFourierKernel (homogeneousOrderedDerivative N j f)) := by
    rw [radianFourier_energy_zero]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    simp only [homogeneousFrequencyEnergy, mul_zero, Real.rpow_zero, one_mul]
  simp_rw [hzero]
  rw [← Finset.mul_sum]
  congr 1
  simp only [homogeneousFrequencyEnergy, mul_zero, Real.rpow_zero, one_mul]
  rw [← integral_finsetSum _ (fun j _ =>
    integrable_schwartz_norm_sq (radianFourierKernel (homogeneousOrderedDerivative N j f)))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [homogeneousOrderedDerivative_fourier_sum]
  congr 1
  rw [← Real.rpow_natCast]
  congr 1
  push_cast
  ring

end DefocusingNLS

end OAI
