import OAI.MathematicalPhysics.Boltzmann.Admissibility

namespace OAI

/-!
# Integrable moments of finite-entropy data

The weighted entropy assumption from the manuscript controls mass, kinetic
energy, absolute entropy, and vector momentum. These conclusions use the actual
integrability assumption rather than any default value of a Bochner integral.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem entropyMoment_nonneg {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    0 ≤ entropyMoment f z := by
  unfold entropyMoment
  positivity

theorem density_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    f z ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (sq_nonneg ‖z.2‖),
    mul_nonneg hf (abs_nonneg (Real.log (f z)))]

theorem energyDensity_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    ‖z.2‖ ^ 2 * f z ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (abs_nonneg (Real.log (f z)))]

theorem absEntropyDensity_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    f z * |Real.log (f z)| ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (sq_nonneg ‖z.2‖)]

theorem momentumDensity_norm_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    ‖f z • z.2‖ ≤ entropyMoment f z := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]
  unfold entropyMoment
  apply mul_le_mul_of_nonneg_left _ hf
  nlinarith [sq_nonneg (‖z.2‖ - 1), abs_nonneg (Real.log (f z))]

namespace FiniteEntropyDatum

variable {f : Density} (hf : FiniteEntropyDatum f)

include hf

/-- Finite weighted entropy gives finite mass. -/
theorem integrable : Integrable f := by
  apply hf.2.2.mono' hf.2.1
  filter_upwards [hf.1] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using density_le_entropyMoment hz

/-- The energy functional integrates an integrable density. -/
theorem integrable_energy : Integrable (fun z => ‖z.2‖ ^ 2 * f z) := by
  have hm : AEStronglyMeasurable (fun z : Phase => ‖z.2‖ ^ 2) := by fun_prop
  apply hf.2.2.mono' (hm.mul hf.2.1)
  filter_upwards [hf.1] with z hz
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hz)]
  exact energyDensity_le_entropyMoment hz

/-- This is absolute entropy, including the convention at zero from the model. -/
theorem integrable_absEntropy : Integrable (fun z => f z * |Real.log (f z)|) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (f z)) :=
    hf.2.1.aemeasurable.log.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun z => f z * |Real.log (f z)|) := by
    simpa only [Pi.mul_def, Real.norm_eq_abs] using hf.2.1.mul hlog.norm
  apply hf.2.2.mono' hm
  filter_upwards [hf.1] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz (abs_nonneg _))]
  exact absEntropyDensity_le_entropyMoment hz

/-- The vector momentum integral is a genuine Bochner integral. -/
theorem integrable_momentum : Integrable (fun z => f z • z.2) := by
  have hm : AEStronglyMeasurable (fun z : Phase => z.2) := by fun_prop
  apply hf.2.2.mono' (hf.2.1.smul hm)
  filter_upwards [hf.1] with z hz
  exact momentumDensity_norm_le_entropyMoment hz

theorem integrable_entropy : Integrable (fun z => f z * Real.log (f z)) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (f z)) :=
    hf.2.1.aemeasurable.log.aestronglyMeasurable
  apply hf.integrable_absEntropy.mono' (hf.2.1.mul hlog)
  filter_upwards [hf.1] with z hz
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hz, le_refl]

end FiniteEntropyDatum

end BoltzmannNonuniqueness

end

end OAI
