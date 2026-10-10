import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerNonlinearEquation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! # Strong Sobolev solutions and the interaction equation -/

open Filter Topology Set MeasureTheory

namespace DefocusingNLS

/-- Differentiability in the lower Sobolev space determines each physical Fourier derivative. -/
theorem hasDerivAt_coordinate_of_lowerSobolev
    (u : ℝ → FourierL2) (g : FourierL2) (t : ℝ) (n : frequencyLattice)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s)) g t) :
    HasDerivAt (fun s => u s n) (((1 + ‖n‖ ^ 2 : ℝ) : ℂ) * g n) t := by
  let E := (lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n).restrictScalars ℝ
  have h := (E.hasFDerivAt.comp_hasDerivAt t hu).const_mul (((1 + ‖n‖ ^ 2 : ℝ) : ℂ))
  have hb : (((1 + ‖n‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + ‖n‖ ^ 2 by positivity))
  convert h using 1
  · funext s
    change u s n = (((1 + ‖n‖ ^ 2 : ℝ) : ℂ)) *
      ((((1 + ‖n‖ ^ 2)⁻¹ : ℝ) : ℂ) * u s n)
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  · rfl

/-- Every strong solution has the expected scalar Fourier differential equations. -/
theorem hasDerivAt_coordinate_schrodinger
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2)
    (t : ℝ) (n : frequencyLattice)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) :
    HasDerivAt (fun s => u s n)
      (-Complex.I * ((‖n‖ ^ 2 : ℝ) : ℂ) * u t n -
        Complex.I * sobolevOddPower k hk m (u t) n) t := by
  have h := hasDerivAt_coordinate_of_lowerSobolev u _ t n hu
  apply h.congr_deriv
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lowerSobolevGenerator_apply, lowerSobolevInclusion_apply,
    Complex.ofReal_div, Complex.ofReal_inv]
  have hb : (((1 + ‖n‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + ‖n‖ ^ 2 by positivity))
  field_simp [hb]

/-- Multiplying by the inverse free phase cancels the unbounded linear term coordinatewise. -/
theorem hasDerivAt_interaction_coordinate
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2)
    (t : ℝ) (n : frequencyLattice)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) :
    HasDerivAt (fun s => schrodingerFlow (-s) (u s) n)
      (((-Complex.I) • schrodingerFlow (-t) (sobolevOddPower k hk m (u t))) n) t := by
  have hp : HasDerivAt (fun s => schrodingerMultiplier (-s) n)
      (Complex.I * ((‖n‖ ^ 2 : ℝ) : ℂ) * schrodingerMultiplier (-t) n) t := by
    have h := (hasDerivAt_schrodingerMultiplier_mul n 1 (-t)).scomp t (hasDerivAt_neg t)
    convert h using 1
    · funext s
      simp
    · simp only [mul_one, neg_smul, one_smul]
      ring
  have h := hp.mul (hasDerivAt_coordinate_schrodinger k hk m u t n hu)
  apply h.congr_deriv
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, schrodingerFlow_apply]
  ring

end DefocusingNLS

end OAI
