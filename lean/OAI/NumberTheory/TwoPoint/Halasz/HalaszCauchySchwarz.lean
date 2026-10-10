import OAI.NumberTheory.TwoPoint.Halasz.HalaszCauchyMeanSquare
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The finite-interval Cauchy--Schwarz step of the triple convolution.
One factor keeps its unweighted prime mean square; the second uses the
Cauchy weight from Perron's kernel. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t) :
    (∫ t in a..b, f t * g t) ≤
      Real.sqrt (∫ t in a..b, f t ^ 2) * Real.sqrt (∫ t in a..b, g t ^ 2) := by
  let μ := volume.restrict (Set.Ioc a b)
  have hfm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hfs : Integrable (fun t => f t ^ 2) μ :=
    ((hf.pow 2).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hgs : Integrable (fun t => g t ^ 2) μ :=
    ((hg.pow 2).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hfl : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).mpr hfs
  have hgl : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).mpr hgs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfl) (by simpa using hgl)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  simpa only [intervalIntegral.integral_of_le hab, μ] using h

lemma halasz_weighted_integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b)
    (P Q : ℝ → ℂ) (hP : Continuous P) (hQ : Continuous Q) :
    (∫ t in a..b, ‖P t‖ * ‖Q t‖ / Real.sqrt (1 + t ^ 2)) ≤
      Real.sqrt (∫ t in a..b, ‖P t‖ ^ 2) *
        Real.sqrt (∫ t in a..b, ‖Q t‖ ^ 2 * (1 + t ^ 2)⁻¹) := by
  have hg : Continuous (fun t => ‖Q t‖ / Real.sqrt (1 + t ^ 2)) := by
    exact hQ.norm.div ((continuous_const.add (continuous_id.pow 2)).sqrt)
      (fun t => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have h := halasz_integral_cauchy_schwarz hab (fun t => ‖P t‖)
    (fun t => ‖Q t‖ / Real.sqrt (1 + t ^ 2)) hP.norm hg (fun _ => norm_nonneg _)
    (fun _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have he (t : ℝ) : (‖Q t‖ / Real.sqrt (1 + t ^ 2)) ^ 2 =
      ‖Q t‖ ^ 2 * (1 + t ^ 2)⁻¹ := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    rfl
  simp_rw [he] at h
  simpa only [mul_div_assoc] using h

end TwoPointCorrelations

end OAI
