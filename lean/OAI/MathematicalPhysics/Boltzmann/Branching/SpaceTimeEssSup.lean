import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss

namespace OAI

/-! # Essential uniform size for bounded spacetime representatives -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.SpaceTimeEssSup

def size (f : ℝ × JetPrototype.Phase → ℝ) : ℝ :=
  (eLpNorm f ∞ WeightedLocal.spacetimeVolume).toReal

theorem nonneg (f : ℝ × JetPrototype.Phase → ℝ) : 0 ≤ size f := ENNReal.toReal_nonneg

theorem ae_abs_le_size {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ u, |f u| ≤ R) : ∀ᵐ u ∂WeightedLocal.spacetimeVolume, |f u| ≤ size f := by
  have hm : MemLp f ∞ WeightedLocal.spacetimeVolume :=
    memLp_top_of_bound hfm.aestronglyMeasurable R (ae_of_all _ (fun u => by
      simpa only [Real.norm_eq_abs] using hf u))
  simpa only [Real.norm_eq_abs,← toReal_eLpNorm,size] using ae_le_lpNorm_exponent_top hm

theorem size_le_ae {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ᵐ u ∂WeightedLocal.spacetimeVolume, |f u| ≤ R) : size f ≤ R := by
  have h : eLpNorm f ∞ WeightedLocal.spacetimeVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top hfm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (hf.mono (fun u hu => by
      simpa only [Real.norm_eq_abs] using hu))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end BoltzmannNonuniqueness.SpaceTimeEssSup

end

end OAI
