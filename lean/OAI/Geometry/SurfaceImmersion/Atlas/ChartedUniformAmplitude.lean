import OAI.Geometry.SurfaceImmersion.Geometry.UniformTrialAmplitude
import OAI.Geometry.SurfaceImmersion.Atlas.ChartedTrialAmplitude

namespace OAI

/-! Uniform bounds on the actual supported trial amplitudes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_trial_amplitude {V : Set SmallModes.Base} (hV : IsOpen V)
    {ρ R : ℝ} (hρ : 0 < ρ) (m : ℕ) (A I Q Ψ : ℝ)
    (hI : 1 ≤ I) (hQ : 1 ≤ Q) (hΨ : 1 ≤ Ψ) :
    let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ {n : ℕ} {P : Fin 3 → Fin n → Expression}
      {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (ψ : SupportedField (F := ℝ) c.chartCompact)
      (Qf : SmallModes.Base → Tensor →L[ℝ] ℝ)
      (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Qf c.e c.e.symm)
      (d : Budgets c.e.source c.e.target s c.realMap ψ Qf c.e c.e.symm),
      c.e.target = V → d.inv m = I → d.forms m = Q → d.psi m = Ψ →
      0 < (s : ℝ) → s ≤ 1 →
      ∀ (B C : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ A → 0 ≤ D →
      ContDiffOn ℝ ∞ B c.e.source → ContDiffOn ℝ ∞ C c.e.source →
      InTrialBall c.e.source reference r B → InTrialBall c.e.source reference r C →
      WeightedBound c.e.source s m A B → WeightedBound c.e.source s m A C →
      WeightedBound c.e.source s m D (B - C) →
      supportedWeightedSeminorm c.chartCompact s m (c.trialAmplitude ψ Qf h hρ B) ≤ A₀ ∧
      supportedWeightedSeminorm c.chartCompact s m (c.trialAmplitude ψ Qf h hρ C) ≤ A₀ ∧
      supportedWeightedSeminorm c.chartCompact s m
        (c.trialAmplitude ψ Qf h hρ B - c.trialAmplitude ψ Qf h hρ C) ≤ A₀ * J * D := by
  obtain ⟨A₀,hA₀,ha⟩ := uniform_local_amplitude_bounds (R := R) hV hρ m A I Q Ψ hI hQ hΨ
  refine ⟨A₀,hA₀,?_⟩
  intro n P ε τ G hG φ K s c r reference ψ Qf h d hv hi hq hψ hs hs1 B C D hA hD hB hC
    hballB hballC hbB hbC hbD
  rw [← hv] at ha
  obtain ⟨hu,hv',hd⟩ := ha c.e.source s r reference c.realMap ψ Qf c.e c.e.symm h d
    hi hq hψ hs hs1 B C D hA hD hB hC hballB hballC hbB hbC hbD
  let b := c.trialAmplitude ψ Qf h hρ B
  let e := c.trialAmplitude ψ Qf h hρ C
  have heb : (b : SmallModes.Base → ℝ) = RootMean.phaseAmplitude ψ (coefficient Qf c.e.symm B) :=
    funext (c.trialAmplitude_apply ψ Qf h hρ hB hballB)
  have hec : (e : SmallModes.Base → ℝ) = RootMean.phaseAmplitude ψ (coefficient Qf c.e.symm C) :=
    funext (c.trialAmplitude_apply ψ Qf h hρ hC hballC)
  let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hA0 : 0 ≤ A₀ := zero_le_one.trans hA₀
  have hD0 : 0 ≤ A₀ * J * D := mul_nonneg (mul_nonneg hA0 hJ) hD
  have hb : WeightedBound c.e.target s m A₀ b := by simpa only [heb] using hu
  have he : WeightedBound c.e.target s m A₀ e := by simpa only [hec] using hv'
  have hdiff : WeightedBound c.e.target s m (A₀ * J * D) (b - e) := by
    change WeightedBound c.e.target s m _ (fun x => b x - e x)
    simpa only [heb,hec] using hd
  have hsp := chartSupport_subset c.e (modeSupport K) c.supportChart
  exact ⟨supportedSeminorm_le_of_weightedBound hs hA0 b
      (hb.extend_support c.e.open_target (b.tsupport_subset.trans hsp) hA0),
    supportedSeminorm_le_of_weightedBound hs hA0 e
      (he.extend_support c.e.open_target (e.tsupport_subset.trans hsp) hA0),
    supportedSeminorm_le_of_weightedBound hs hD0 (b - e)
      (hdiff.extend_support c.e.open_target ((b - e).tsupport_subset.trans hsp) hD0)⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
