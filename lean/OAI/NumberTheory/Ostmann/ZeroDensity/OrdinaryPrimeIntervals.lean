import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedProgressionInputs

namespace OAI

/-! # The ordinary prime interval and its normalization

The conductor-one character is trivial, so the ordinary prime prior has
no Page correction. Its logarithmic interval mass and inverse bound are
derived from the same published theta input.
-/

namespace Ostmann

open Filter MeasureTheory

theorem PrimitiveRealZero.modulus_ne_one (e : PrimitiveRealZero) : e.modulus ≠ 1 := by
  let : NeZero e.modulus := ⟨Nat.ne_of_gt e.positive⟩
  intro h
  apply e.nontrivial
  exact (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := e.character)).mpr (e.primitive.trans h)

theorem PublishedProgressionInput.localZero_one (P : PublishedProgressionInput) :
    P.localZero 1 = none := by
  cases he : P.localZero 1 with
  | none => rfl
  | some e => exact False.elim (e.modulus_ne_one (Nat.dvd_one.mp (P.divides 1 e he)))

theorem PublishedProgressionInput.ordinary_log_interval (P : PublishedProgressionInput)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp t) - Real.log (t / s)| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) := by
  have h := P.local_log_interval 1 0 (by norm_num) (by norm_num) hs hst hshort
  rw [P.localZero_one] at h
  simp only [pageCoefficient, pageBeta, Nat.totient_one, Nat.cast_one,
    primeLogDensity, zero_mul, sub_zero, one_mul] at h
  rw [← intervalIntegral.integral_of_le hst,
    integral_one_div_of_pos (by linarith) (by linarith)] at h
  exact h

theorem log_unit_ratio_lower {s : ℝ} (hs : 0 < s) :
    1 / (s + 1) ≤ Real.log ((s + 1) / s) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (s + 1) / s)
    (div_pos (by linarith) hs)
  have heq : 1 - ((s + 1) / s)⁻¹ = 1 / (s + 1) := by
    field_simp
    ring
  rwa [heq] at h

theorem theta_log_error_small (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ s : ℝ in atTop,
      18 * C * Real.exp (-c * Real.sqrt s) ≤ 1 / (2 * (s + 1)) := by
  have hpow := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp
    Real.tendsto_sqrt_atTop
  have hlin : Tendsto (fun s : ℝ => s * Real.exp (-c * Real.sqrt s)) atTop (nhds 0) := by
    apply hpow.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    dsimp only [Function.comp_def]
    rw [Real.rpow_two, Real.sq_sqrt hs]
  have hzero := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp
    Real.tendsto_sqrt_atTop
  simp only [Real.rpow_zero, one_mul, Function.comp_def] at hzero
  have hsum : Tendsto (fun s : ℝ =>
      (s + 1) * (18 * C * Real.exp (-c * Real.sqrt s))) atTop (nhds 0) := by
    have hb : Tendsto (fun s : ℝ => 18 * C *
        (s * Real.exp (-c * Real.sqrt s) + Real.exp (-c * Real.sqrt s))) atTop (nhds 0) := by
      simpa only [add_zero, mul_zero] using ((hlin.add hzero).const_mul (18 * C))
    exact hb.congr (fun s => by ring)
  filter_upwards [hsum.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℝ)] with s hsmall hs
  apply (le_div_iff₀ (by positivity : 0 < 2 * (s + 1))).mpr
  nlinarith

theorem PublishedProgressionInput.ordinary_interval_lower (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop,
      1 / (2 * (s + 1)) ≤ reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp (s + 1)) := by
  filter_upwards [theta_log_error_small P.errorConstant P.decay P.decay_pos,
    eventually_ge_atTop (1 : ℝ)] with s herr hs
  have h := P.ordinary_log_interval hs (by linarith : s ≤ s + 1) le_rfl
  have hlower := log_unit_ratio_lower (by linarith : 0 < s)
  have hhalf : 1 / (s + 1) = 2 * (1 / (2 * (s + 1))) := by field_simp
  have hh := (abs_le.mp h).1
  linarith

/-- The normalizing reciprocal costs only a factor linear in the log
coordinate, exactly as required by the arithmetic idealization. -/
theorem PublishedProgressionInput.ordinary_normalization_bound (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop,
      0 < reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp (s + 1)) ∧
      (reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp (s + 1)))⁻¹ ≤ 2 * (s + 1) := by
  filter_upwards [P.ordinary_interval_lower, eventually_ge_atTop (1 : ℝ)] with s hS hs
  have hpos : 0 < (1 : ℝ) / (2 * (s + 1)) := by positivity
  refine ⟨hpos.trans_le hS, ?_⟩
  have hi := one_div_le_one_div_of_le hpos hS
  simpa only [one_div, inv_inv] using hi

end Ostmann

end OAI
