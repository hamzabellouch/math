import OAI.Geometry.SurfaceImmersion.Correction.CombinedMeanTensor
import OAI.Geometry.Immersion.ClosedSurface.LocalMean

namespace OAI

/-! Actual supported phase amplitudes for arbitrary trial tensor fields.
On the admissible trial ball they equal the cutoff square root, and their
finite-loss bounds follow from the fixed positive coefficient margins. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean
open JetPolynomial (SupportedField supportedWeightedSeminorm supportedSeminorm_le_of_weightedBound)

variable {U V : Set Base} {s r ρ R₀ : ℝ} {reference : Base → Tensor}
  {F : RField 4} {K : Compacts JetPolynomial.Base}
  {ψ : SupportedField (F := ℝ) (JetPolynomial.Perturbation.modeSupport K)}
  {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

def supportedTrialAmplitude (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (JetPolynomial.Perturbation.modeSupport K : Set Base) ⊆ V)
    (A : Base → Tensor) : SupportedField (F := ℝ) (JetPolynomial.Perturbation.modeSupport K) :=
  by
  classical
  exact if ha : ContDiffOn ℝ ∞ A U ∧ InTrialBall U reference r A then
    supportedRootAmplitude h.domain.isOpen _ hKV ψ (coefficient Q e A)
      (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto ha.1)
      (fun _ hp => hρ.trans_le (coefficient_trial_range h.invInto h.margin ha.2 hp).1)
  else 0

lemma supportedTrialAmplitude_apply (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (JetPolynomial.Perturbation.modeSupport K : Set Base) ⊆ V)
    {A : Base → Tensor} (hA : ContDiffOn ℝ ∞ A U) (hball : InTrialBall U reference r A) (x : Base) :
    supportedTrialAmplitude h hρ hKV A x = phaseAmplitude ψ (coefficient Q e A) x := by
  classical
  simp only [supportedTrialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A U ∧
    InTrialBall U reference r A from ⟨hA, hball⟩)]
  rfl

lemma supportedTrialAmplitude_function (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (JetPolynomial.Perturbation.modeSupport K : Set Base) ⊆ V)
    {A : Base → Tensor} (hA : ContDiffOn ℝ ∞ A U) (hball : InTrialBall U reference r A) :
    (supportedTrialAmplitude h hρ hKV A : Base → ℝ) = phaseAmplitude ψ (coefficient Q e A) := by
  funext x
  exact supportedTrialAmplitude_apply h hρ hKV hA hball x

theorem supportedTrialAmplitude_bounds (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ)
    (hKV : (JetPolynomial.Perturbation.modeSupport K : Set Base) ⊆ V) (n : ℕ) (C : ℝ) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (A B : Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      InTrialBall U reference r A → InTrialBall U reference r B →
      WeightedBound U s n C A → WeightedBound U s n C B → WeightedBound U s n D (A - B) →
      supportedWeightedSeminorm (JetPolynomial.Perturbation.modeSupport K) ⟨s, hs.le⟩ n
        (supportedTrialAmplitude h hρ hKV A) ≤ A₀ ∧
      supportedWeightedSeminorm (JetPolynomial.Perturbation.modeSupport K) ⟨s, hs.le⟩ n
        (supportedTrialAmplitude h hρ hKV B) ≤ A₀ ∧
      supportedWeightedSeminorm (JetPolynomial.Perturbation.modeSupport K) ⟨s, hs.le⟩ n
        (supportedTrialAmplitude h hρ hKV A - supportedTrialAmplitude h hρ hKV B) ≤
          A₀ * inputFactor d n * D := by
  obtain ⟨A₀, hA₀, ha⟩ := h.amplitude_bounds d hs hs1 hρ n C
  refine ⟨A₀, hA₀, ?_⟩
  intro A B D hC hD hA hB hballA hballB hbA hbB hbD
  obtain ⟨hu, hv, hd⟩ := ha A B D hC hD hA hB hballA hballB hbA hbB hbD
  let a := supportedTrialAmplitude h hρ hKV A
  let b := supportedTrialAmplitude h hρ hKV B
  have heA := supportedTrialAmplitude_function h hρ hKV hA hballA
  have heB := supportedTrialAmplitude_function h hρ hKV hB hballB
  have hA0 : 0 ≤ A₀ := zero_le_one.trans hA₀
  have hD0 : 0 ≤ A₀ * inputFactor d n * D := mul_nonneg (mul_nonneg hA0 (inputFactor_nonneg d n)) hD
  have hau : WeightedBound V s n A₀ a := by simpa only [a, heA] using hu
  have hav : WeightedBound V s n A₀ b := by simpa only [b, heB] using hv
  have had : WeightedBound V s n (A₀ * inputFactor d n * D) (a - b) := by
    change WeightedBound V s n (A₀ * inputFactor d n * D) (fun p => a p - b p)
    simpa only [a, b, heA, heB] using hd
  exact ⟨supportedSeminorm_le_of_weightedBound (s := ⟨s, hs.le⟩) hs hA0 a
      (hau.extend_support h.domain.isOpen (a.tsupport_subset.trans hKV) hA0),
    supportedSeminorm_le_of_weightedBound (s := ⟨s, hs.le⟩) hs hA0 b
      (hav.extend_support h.domain.isOpen (b.tsupport_subset.trans hKV) hA0),
    supportedSeminorm_le_of_weightedBound (s := ⟨s, hs.le⟩) hs hD0 (a - b)
      (had.extend_support h.domain.isOpen ((a - b).tsupport_subset.trans hKV) hD0)⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
