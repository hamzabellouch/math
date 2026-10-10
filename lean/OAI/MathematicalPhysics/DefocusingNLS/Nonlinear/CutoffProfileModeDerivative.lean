import OAI.MathematicalPhysics.DefocusingNLS.Certificates.CompactFamilyIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMovingPath

namespace OAI

/-! # Time derivative of the actual cutoff-profile Fourier coefficients

The physical volume factor disappears after rescaling to the fixed cutoff.
Differentiating then takes place on a fixed compact support.
-/

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffProfile_coefficient_fixed_scale (R : ℝ) (hR : 0 < R)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : frequencyLattice) :
    schwartzLatticeCoefficient R (radianFourierKernel (cutoffProfileSchwartz R hR χ hχ Q hQ)) n =
      schwartzLatticeCoefficient 1 (radianFourierKernel (compactDilationFamily χ hχ Q hQ R)) n := by
  have he : cutoffProfileSchwartz R hR χ hχ Q hQ =
      schwartzPhysicalDilation 0 R hR (compactDilationFamily χ hχ Q hQ R) := by
    ext x
    simp only [cutoffProfileSchwartz_apply, schwartzPhysicalDilation_apply,
      compactDilationFamily_apply, mul_zero, Real.rpow_zero, Complex.ofReal_one,
      one_mul, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [he, radianFourierKernel_schwartzPhysicalDilation,
    schwartzLatticeCoefficient_homogeneousDilation 0 R R hR hR]
  simp only [mul_zero, Real.rpow_zero, Complex.ofReal_one,
    one_mul, div_self hR.ne']

private theorem hasDerivAt_radius (L s : ℝ) :
    HasDerivAt (expandingRadius L) (expandingRadius L s / 2) s := by
  change HasDerivAt (fun t : ℝ => L * Real.exp (t / 2)) _ s
  apply (((hasDerivAt_id s).div_const 2).exp.const_mul L).congr_deriv
  dsimp only [expandingRadius, id_eq]
  ring

private theorem positive_radius (L t : ℝ) (hL : 0 < L) : 0 < expandingRadius L t :=
  mul_pos hL (Real.exp_pos _)

/-- An exact scalar Fourier-mode derivative at every real time. -/
theorem hasDerivAt_cutoffProfile_coefficient (L s : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : frequencyLattice) :
    HasDerivAt
      (fun t => schwartzLatticeCoefficient (expandingRadius L t)
        (radianFourierKernel (cutoffProfileSchwartz (expandingRadius L t)
          (positive_radius L _ hL) χ hχ Q hQ)) n)
      ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) *
        radianFourierIntegral (fun x => χ x *
          fderiv ℝ Q ((expandingRadius L s) • x) ((expandingRadius L s / 2) • x))
          (n : E)) s := by
  let F : ℝ → E → ℂ := fun t x => χ x * Q ((expandingRadius L t) • x)
  let Fd : ℝ → E → ℂ := fun t x => χ x *
    fderiv ℝ Q ((expandingRadius L t) • x) ((expandingRadius L t / 2) • x)
  have hRc : Continuous (expandingRadius L) := by unfold expandingRadius; fun_prop
  have harg : Continuous (fun p : ℝ × E => (expandingRadius L p.1) • p.2) :=
    (hRc.comp continuous_fst).smul continuous_snd
  have hFc : Continuous (Function.uncurry F) :=
    (χ.continuous.comp continuous_snd).mul (hQ.continuous.comp harg)
  have hFdc : Continuous (Function.uncurry Fd) :=
    (χ.continuous.comp continuous_snd).mul
      (((contDiff_infty_iff_fderiv.mp hQ).2.continuous.comp harg).clm_apply
        (((hRc.comp continuous_fst).div_const 2).smul continuous_snd))
  have hd (t : ℝ) (x : E) : HasDerivAt (fun u => F u x) (Fd t x) t :=
    (((hQ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_radius L t).smul_const x)).const_mul (χ x))
  have hz (_t : ℝ) (x : E) (hx : x ∉ tsupport (χ : E → ℂ)) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  have h := (hasDerivAt_compactFamily_fourier F Fd hFc hFdc
    (tsupport (χ : E → ℂ)) hχ
    (fun t x hx => by dsimp [F]; rw [hz t x hx, zero_mul])
    (fun t x hx => by dsimp [Fd]; rw [hz t x hx, zero_mul]) hd s (n : E)).const_mul
      ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ)
  have he (t : ℝ) :
      schwartzLatticeCoefficient (expandingRadius L t)
        (radianFourierKernel (cutoffProfileSchwartz (expandingRadius L t)
          (positive_radius L _ hL) χ hχ Q hQ)) n =
      ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) * radianFourierIntegral (F t) (n : E) := by
    rw [cutoffProfile_coefficient_fixed_scale]
    simp only [schwartzLatticeCoefficient, mul_one, inv_one, one_smul,
      radianFourierKernel_apply, F]
    rfl
  simpa only [he, Fd] using h

end DefocusingNLS

end OAI
