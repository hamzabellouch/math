import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! # Exact frozen-potential energy cancellation

The principal odd-power linearization is skew for its positive anisotropic
quadratic form.  This is the scalar cancellation needed before estimating
spatially varying coefficients and lower derivatives.
-/

open scoped ComplexConjugate

namespace DefocusingNLS

theorem oddPowerDerivative_rotated (m : ℕ) (q v : ℂ) :
    star q * oddPowerDerivative m q v =
      ((Complex.normSq q) ^ m : ℝ) *
        (((m + 1 : ℕ) : ℂ) * (star q * v) + (m : ℂ) * star (star q * v)) := by
  have hp : (((Complex.normSq q) ^ m : ℝ) : ℂ) = q ^ m * star q ^ m := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj q, mul_pow]
    rfl
  rw [hp]
  cases m with
  | zero => simp [oddPowerDerivative]
  | succ m =>
      simp only [oddPowerDerivative, add_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul, Nat.succ_sub_one,
        star_mul, star_star, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem oddPowerLinearization_rotated_components (m : ℕ) (q v : ℂ) :
    (star q * (-Complex.I * oddPowerDerivative m q v)).re =
        Complex.normSq q ^ m * (star q * v).im ∧
      (star q * (-Complex.I * oddPowerDerivative m q v)).im =
        -(2 * (m : ℝ) + 1) * Complex.normSq q ^ m * (star q * v).re := by
  have he : star q * (-Complex.I * oddPowerDerivative m q v) =
      -Complex.I * (star q * oddPowerDerivative m q v) := by ring
  rw [he, oddPowerDerivative_rotated]
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im,
    Complex.conj_re, Complex.conj_im, zero_mul,
    sub_zero, zero_sub, zero_add, add_zero, one_mul, neg_mul]
  push_cast
  constructor <;> ring

noncomputable def frozenHamiltonianEnergy (m : ℕ) (q v : ℂ) : ℝ :=
  (2 * (m : ℝ) + 1) * (star q * v).re ^ 2 + (star q * v).im ^ 2

theorem frozenHamiltonianEnergy_bounds (m : ℕ) (q v : ℂ) :
    ‖q‖ ^ 2 * ‖v‖ ^ 2 ≤ frozenHamiltonianEnergy m q v ∧
      frozenHamiltonianEnergy m q v ≤ (2 * (m : ℝ) + 1) * ‖q‖ ^ 2 * ‖v‖ ^ 2 := by
  have hnorm : (star q * v).re ^ 2 + (star q * v).im ^ 2 = ‖q‖ ^ 2 * ‖v‖ ^ 2 := by
    calc
      _ = Complex.normSq (star q * v) := by simp [Complex.normSq_apply, pow_two]
      _ = ‖star q * v‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ = _ := by rw [norm_mul, norm_star, mul_pow]
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  unfold frozenHamiltonianEnergy
  constructor
  · rw [← hnorm]
    nlinarith [mul_nonneg hm (sq_nonneg (star q * v).re)]
  · calc
      _ ≤ (2 * (m : ℝ) + 1) * ((star q * v).re ^ 2 + (star q * v).im ^ 2) := by
        nlinarith [mul_nonneg hm (sq_nonneg (star q * v).im)]
      _ = _ := by rw [hnorm]; ring

theorem frozenHamiltonianEnergy_cancellation (m : ℕ) (q v : ℂ) :
    2 * (2 * (m : ℝ) + 1) * (star q * v).re *
        (star q * (-Complex.I * oddPowerDerivative m q v)).re +
      2 * (star q * v).im *
        (star q * (-Complex.I * oddPowerDerivative m q v)).im = 0 := by
  obtain ⟨hr, hi⟩ := oddPowerLinearization_rotated_components m q v
  rw [hr, hi]
  ring

theorem hasDerivAt_frozenHamiltonianEnergy (m : ℕ) (q : ℂ)
    (v : ℝ → ℂ) (t : ℝ)
    (hv : HasDerivAt v (-Complex.I * oddPowerDerivative m q (v t)) t) :
    HasDerivAt (fun s => frozenHamiltonianEnergy m q (v s)) 0 t := by
  have hu := hv.const_mul (star q)
  have hur := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hu
  have hui := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hu
  simp only [Complex.reCLM_apply] at hur
  simp only [Complex.imCLM_apply] at hui
  have hr := ((hur.pow 2).const_mul (2 * (m : ℝ) + 1)).add (hui.pow 2)
  convert! hr using 1
  have hc := frozenHamiltonianEnergy_cancellation m q (v t)
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Nat.reduceSub, pow_one, Nat.cast_ofNat]
  nlinarith [hc]

noncomputable def normalizedFrozenHamiltonianEnergy (m : ℕ) (q v : ℂ) : ℝ :=
  frozenHamiltonianEnergy m q v / ‖q‖ ^ 2

/-- Dividing by the frozen amplitude gives coercivity independent of that amplitude. -/
theorem normalizedFrozenHamiltonianEnergy_bounds (m : ℕ) (q v : ℂ) (hq : q ≠ 0) :
    ‖v‖ ^ 2 ≤ normalizedFrozenHamiltonianEnergy m q v ∧
      normalizedFrozenHamiltonianEnergy m q v ≤ (2 * (m : ℝ) + 1) * ‖v‖ ^ 2 := by
  have hp : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  obtain ⟨hl, hu⟩ := frozenHamiltonianEnergy_bounds m q v
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa only [mul_comm] using hl
  · apply (div_le_iff₀ hp).mpr
    nlinarith [hu]

theorem hasDerivAt_normalizedFrozenHamiltonianEnergy (m : ℕ) (q : ℂ)
    (v : ℝ → ℂ) (t : ℝ)
    (hv : HasDerivAt v (-Complex.I * oddPowerDerivative m q (v t)) t) :
    HasDerivAt (fun s => normalizedFrozenHamiltonianEnergy m q (v s)) 0 t := by
  simpa only [normalizedFrozenHamiltonianEnergy, zero_div] using!
    (hasDerivAt_frozenHamiltonianEnergy m q v t hv).div_const (‖q‖ ^ 2)

end DefocusingNLS

end OAI
