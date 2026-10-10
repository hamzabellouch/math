import OAI.NumberTheory.DukePrimeDegree.Dynamics.ErgodicAverageMean
import OAI.NumberTheory.DukePrimeDegree.Dynamics.DominatedAverages

namespace OAI

/-!
# L1 control of actual ergodic orbit averages

Probability normalization gives the L2-to-L1 bound with constant one.
Combining it with the identified mean and the uniform-density transfer
allows the sampling law of an orbit average to vary with its length.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma integral_norm_le_L2_norm (μ : Measure X) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

lemma L1_tendsto_of_L2_tendsto_constant
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : ℕ → Lp ℝ 2 μ) (c : ℝ)
    (hF : Tendsto F atTop (𝓝 (constantL2 μ c))) :
    Tendsto (fun n => ∫ x, |F n x - c| ∂μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (∫ x, |F n x - c| ∂μ) ≤ ‖F n - constantL2 μ c‖ := by
    have he : (∫ x, |F n x - c| ∂μ) = ∫ x, ‖(F n - constantL2 μ c) x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (F n) (constantL2 μ c), constantL2_ae μ c] with x hx hc
      simp only [hx, Pi.sub_apply, hc, Real.norm_eq_abs]
    rw [he]
    exact integral_norm_le_L2_norm μ _
  have hnorm : Tendsto (fun n => ‖F n - constantL2 μ c‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hF.sub_const (constantL2 μ c)).norm
  exact squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _)) hbound hnorm

/-- The actual L2 Cesaro averages have vanishing L1 error from the
original integral. -/
theorem L1_orbit_average_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Ergodic T μ) (f : Lp ℝ 2 μ) :
    Tendsto (fun N => ∫ x,
      |(birkhoffAverage ℝ (Lp.compMeasurePreserving T hT.toMeasurePreserving) id N f) x -
        ∫ y, f y ∂μ| ∂μ) atTop (𝓝 0) :=
  L1_tendsto_of_L2_tendsto_constant μ _ _ (L2_orbit_average_tendsto_integral μ T hT f)

/-- Uniformly dominated initial sampling laws have the same average
limit even when their law changes at each averaging length. -/
theorem dominated_orbit_average_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Ergodic T μ) (f : Lp ℝ 2 μ)
    (ν : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ν n)]
    (C : ℝ) (hC : 0 ≤ C) (hdom : ∀ n, ν n ≤ ENNReal.ofReal C • μ) :
    Tendsto (fun N => ∫ x,
      (birkhoffAverage ℝ (Lp.compMeasurePreserving T hT.toMeasurePreserving) id N f) x ∂ν N)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply integral_tendsto_of_dominated_sampling μ ν C _ hC hdom
  · intro n
    exact memLp_one_iff_integrable.mp ((Lp.memLp _).mono_exponent (by norm_num))
  · exact L1_orbit_average_tendsto_integral μ T hT f

end DukePrimeDegree

end

end OAI
