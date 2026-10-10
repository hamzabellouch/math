import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLocalAmplitude
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanData

namespace OAI

/-! Polynomial bounds for the actual supported square-root trial amplitude. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

 theorem polynomial_trial_amplitude_bounds (m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < (s : ℝ) → s ≤ 1 → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.budgets.inv m ≤ B → d.budgets.forms m ≤ B → d.budgets.psi m ≤ B →
      ∀ (f g : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ f c.e.source → ContDiffOn ℝ ∞ g c.e.source →
      InTrialBall c.e.source reference r f → InTrialBall c.e.source reference r g →
      WeightedBound c.e.source s m B f → WeightedBound c.e.source s m B g →
      WeightedBound c.e.source s m D (f-g) →
      supportedWeightedSeminorm c.chartCompact s m (d.amplitude hρ f) ≤ C*B^p ∧
      supportedWeightedSeminorm c.chartCompact s m (d.amplitude hρ g) ≤ C*B^p ∧
      supportedWeightedSeminorm c.chartCompact s m
        (d.amplitude hρ f-d.amplitude hρ g) ≤ C*B^p*D := by
  obtain ⟨p,C,hC,hamp⟩ := polynomial_local_amplitude_bounds m
  refine ⟨p,C,hC,?_⟩
  intro n P ε τ G hG φ K s c r ρ R reference d hρ hs hs1 B hB hρB hi hf hp f g D hD
    hfs hgs hfb hgb hbf hbg hdiff
  obtain ⟨hu,hv,hd⟩ := hamp d.localBounds d.budgets hs hs1 hρ B hB hρB hi hf hp
    f g D hD hfs hgs hfb hgb hbf hbg hdiff
  have hef : (d.amplitude hρ f : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm f) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hfs hfb)
  have heg : (d.amplitude hρ g : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm g) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hgs hgb)
  have hC0 : 0 ≤ C*B^p := mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hB) _)
  have hsp := chartSupport_subset c.e (modeSupport K) c.supportChart
  have hb1 : WeightedBound c.e.target s m (C*B^p) (d.amplitude hρ f) := by
    simpa only [hef] using hu
  have hb2 : WeightedBound c.e.target s m (C*B^p) (d.amplitude hρ g) := by
    simpa only [heg] using hv
  have hb3 : WeightedBound c.e.target s m (C*B^p*D) (d.amplitude hρ f-d.amplitude hρ g) := by
    change WeightedBound c.e.target s m _ (fun x => d.amplitude hρ f x-d.amplitude hρ g x)
    simpa only [hef,heg] using hd
  exact ⟨supportedSeminorm_le_of_weightedBound hs hC0 _
      (hb1.extend_support c.e.open_target ((d.amplitude hρ f).tsupport_subset.trans hsp) hC0),
    supportedSeminorm_le_of_weightedBound hs hC0 _
      (hb2.extend_support c.e.open_target ((d.amplitude hρ g).tsupport_subset.trans hsp) hC0),
    supportedSeminorm_le_of_weightedBound hs (mul_nonneg hC0 hD) _
      (hb3.extend_support c.e.open_target
        ((d.amplitude hρ f-d.amplitude hρ g).tsupport_subset.trans hsp) (mul_nonneg hC0 hD))⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
