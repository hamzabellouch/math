import OAI.Geometry.SurfaceImmersion.Correction.ChartedCombinedMeanBounds
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedTrialAmplitude

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

def trialAmplitude (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) :
    SupportedField (F := ℝ) c.chartCompact := by
  classical
  exact if ha : ContDiffOn ℝ ∞ A c.e.source ∧ InTrialBall c.e.source reference r A then
    supportedRootAmplitude h.domain.isOpen c.chartCompact
      (chartSupport_subset c.e (modeSupport K) c.supportChart) ψ (coefficient Q c.e.symm A)
      (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto ha.1)
      (fun _ hp => hρ.trans_le (coefficient_trial_range h.invInto h.margin ha.2 hp).1)
    else 0

lemma trialAmplitude_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A c.e.source) (hball : InTrialBall c.e.source reference r A)
    (y : SmallModes.Base) :
    c.trialAmplitude ψ Q h hρ A y = phaseAmplitude ψ (coefficient Q c.e.symm A) y := by
  classical
  simp only [trialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A c.e.source ∧
    InTrialBall c.e.source reference r A from ⟨hA,hball⟩)]
  rfl

theorem trialAmplitude_bounds
    (d : Budgets c.e.source c.e.target s c.realMap ψ Q c.e c.e.symm)
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hρ : 0 < ρ) (m : ℕ) (C : ℝ) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (A B : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A c.e.source → ContDiffOn ℝ ∞ B c.e.source →
      InTrialBall c.e.source reference r A → InTrialBall c.e.source reference r B →
      WeightedBound c.e.source s m C A → WeightedBound c.e.source s m C B →
      WeightedBound c.e.source s m D (A - B) →
      supportedWeightedSeminorm c.chartCompact s m (c.trialAmplitude ψ Q h hρ A) ≤ A₀ ∧
      supportedWeightedSeminorm c.chartCompact s m (c.trialAmplitude ψ Q h hρ B) ≤ A₀ ∧
      supportedWeightedSeminorm c.chartCompact s m
        (c.trialAmplitude ψ Q h hρ A - c.trialAmplitude ψ Q h hρ B) ≤ A₀ * inputFactor d m * D := by
  obtain ⟨A₀,hA₀,ha⟩ := h.amplitude_bounds d hs hs1 hρ m C
  refine ⟨A₀,hA₀,?_⟩
  intro A B D hC hD hA hB hballA hballB hbA hbB hbD
  obtain ⟨hu,hv,hd⟩ := ha A B D hC hD hA hB hballA hballB hbA hbB hbD
  let a := c.trialAmplitude ψ Q h hρ A
  let b := c.trialAmplitude ψ Q h hρ B
  have heA : (a : SmallModes.Base → ℝ) = phaseAmplitude ψ (coefficient Q c.e.symm A) :=
    funext (c.trialAmplitude_apply ψ Q h hρ hA hballA)
  have heB : (b : SmallModes.Base → ℝ) = phaseAmplitude ψ (coefficient Q c.e.symm B) :=
    funext (c.trialAmplitude_apply ψ Q h hρ hB hballB)
  have hA0 : 0 ≤ A₀ := zero_le_one.trans hA₀
  have hD0 : 0 ≤ A₀ * inputFactor d m * D := mul_nonneg (mul_nonneg hA0 (inputFactor_nonneg d m)) hD
  have hau : WeightedBound c.e.target s m A₀ a := by simpa only [heA] using hu
  have hav : WeightedBound c.e.target s m A₀ b := by simpa only [heB] using hv
  have had : WeightedBound c.e.target s m (A₀ * inputFactor d m * D) (a - b) := by
    change WeightedBound c.e.target s m _ (fun x => a x - b x)
    simpa only [heA, heB] using hd
  have hsp := chartSupport_subset c.e (modeSupport K) c.supportChart
  exact ⟨supportedSeminorm_le_of_weightedBound hs hA0 a
      (hau.extend_support c.e.open_target (a.tsupport_subset.trans hsp) hA0),
    supportedSeminorm_le_of_weightedBound hs hA0 b
      (hav.extend_support c.e.open_target (b.tsupport_subset.trans hsp) hA0),
    supportedSeminorm_le_of_weightedBound hs hD0 (a - b)
      (had.extend_support c.e.open_target ((a - b).tsupport_subset.trans hsp) hD0)⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
