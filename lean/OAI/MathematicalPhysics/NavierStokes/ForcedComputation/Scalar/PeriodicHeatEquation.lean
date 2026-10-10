import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PeriodicHeatSeries

namespace OAI

/-! The time and spatial derivatives of the periodic heat Fourier moments.
The zeroth moment satisfies the one-dimensional heat equation. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open Set
open scoped ContDiff

theorem periodicHeatMoment_time (k : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => periodicHeatMoment k (s, x))
      (-4 * (Real.pi : ℂ) ^ 2 * periodicHeatMoment (k + 2) (t, x)) t := by
  have h := (periodicHeatMoment_hasFDerivAt k ht).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [Function.comp_def, id_eq, periodicHeatMomentDerivative_eq k (p := (t, x)) ht, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply, Complex.ofReal_one,
    Complex.ofReal_zero, smul_zero, add_zero, smul_eq_mul, mul_one, mul_zero] using h

theorem periodicHeatMoment_space (k : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => periodicHeatMoment k (t, y))
      (2 * (Real.pi : ℂ) * Complex.I * periodicHeatMoment (k + 1) (t, x)) x := by
  have h := (periodicHeatMoment_hasFDerivAt k ht).comp_hasDerivAt x
    ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))
  have he : periodicHeatMomentDerivative k (t, x) (0, 1) =
      2 * (Real.pi : ℂ) * Complex.I * periodicHeatMoment (k + 1) (t, x) := by
    simp only [periodicHeatMomentDerivative_eq k (p := (t, x)) ht, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply, Complex.ofReal_one,
      Complex.ofReal_zero, zero_add, smul_eq_mul, mul_one, mul_zero]
    ring
  simpa only [Function.comp_def, id_eq, he] using h

theorem periodicHeatMoment_heat {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => periodicHeatMoment 0 (s, x)) t =
      deriv (fun y => deriv (fun z => periodicHeatMoment 0 (t, z)) y) x := by
  have he : (fun y => deriv (fun z => periodicHeatMoment 0 (t, z)) y) =
      fun y => 2 * (Real.pi : ℂ) * Complex.I * periodicHeatMoment 1 (t, y) := by
    funext y
    exact (periodicHeatMoment_space 0 ht y).deriv
  rw [he, (periodicHeatMoment_time 0 ht x).deriv]
  rw [((periodicHeatMoment_space 1 ht x).const_mul (2 * (Real.pi : ℂ) * Complex.I)).deriv]
  simp only [show (0 + 2 : ℕ) = 2 from rfl]
  ring_nf
  rw [Complex.I_sq]
  ring

end ForcedComputation.VelocityDetector

end

end OAI
