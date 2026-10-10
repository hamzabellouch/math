import OAI.Geometry.Immersion.ClosedSurface.LocalMean

namespace OAI

/-! Uniform square-root amplitude constants from numerical coordinate,
cutoff and form bounds. In particular they precede the scale and map. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

theorem uniform_local_amplitude_bounds {V : Set Base} (hV : IsOpen V)
    {ρ R : ℝ} (hρ : 0 < ρ) (m : ℕ) (C I Q Ψ : ℝ)
    (hI : 1 ≤ I) (hQ : 1 ≤ Q) (hΨ : 1 ≤ Ψ) :
    let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (U : Set Base) (s r : ℝ)
      (reference : Base → Tensor) (F : RField 4) (ψ : Base → ℝ)
      (forms : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base)
      (_h : LocalBounds U V s r ρ R reference F ψ forms χ e)
      (d : Budgets U V s F ψ forms χ e),
      d.inv m = I → d.forms m = Q → d.psi m = Ψ → 0 < s → s ≤ 1 →
      ∀ (A B : Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      InTrialBall U reference r A → InTrialBall U reference r B →
      WeightedBound U s m C A → WeightedBound U s m C B →
      WeightedBound U s m D (A - B) →
      WeightedBound V s m A₀ (phaseAmplitude ψ (coefficient forms e A)) ∧
      WeightedBound V s m A₀ (phaseAmplitude ψ (coefficient forms e B)) ∧
      WeightedBound V s m (A₀ * J * D)
        (fun x => phaseAmplitude ψ (coefficient forms e A) x -
          phaseAmplitude ψ (coefficient forms e B) x) := by
  dsimp only
  let J := 2 ^ m * Q * (m.factorial : ℝ) * I ^ m
  let C' := max 1 (J * C)
  obtain ⟨A₀,hA₀,ha⟩ := compact_amplitude_bounds (R := R) hV.uniqueDiffOn hρ
    (show 1 ≤ C' from le_max_left _ _) (zero_le_one.trans hΨ) m
  refine ⟨A₀,hA₀,?_⟩
  intro U s r reference F ψ forms χ e h d hi hq hψ hs hs1 A B D hC hD hA hB hballA hballB hbA hbB hbD
  have heq : inputFactor d m = J := by simp only [inputFactor, hi, hq, J]
  have hcoeff (X : Base → Tensor) (hX : ContDiffOn ℝ ∞ X U)
      (hbX : WeightedBound U s m C X) : WeightedBound V s m C' (coefficient forms e X) := by
    have hh := weighted_coefficient h.openU.uniqueDiffOn hV.uniqueDiffOn hs hs1
      (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hC h.smoothQ h.smoothInv
      h.invInto hX (d.inv_bound m) (d.forms_bound m) hbX
    change WeightedBound V s m (inputFactor d m * C) _ at hh
    rw [heq] at hh
    exact hh.mono_const (le_max_right _ _)
  have hdiff := weighted_coefficient_difference h.openU.uniqueDiffOn hV.uniqueDiffOn
    hs hs1 (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hD h.smoothQ h.smoothInv
    h.invInto hA hB (d.inv_bound m) (d.forms_bound m) hbD
  change WeightedBound V s m (inputFactor d m * D) _ at hdiff
  rw [heq] at hdiff
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hcut : WeightedBound V s m Ψ ψ := by simpa only [hψ] using d.psi_bound m
  have hh := ha s (J * D) ψ (coefficient forms e A) (coefficient forms e B) hs
    (mul_nonneg hJ hD) h.smoothPsi
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hB)
    (coefficient_trial_range h.invInto h.margin hballA)
    (coefficient_trial_range h.invInto h.margin hballB) hcut (hcoeff A hA hbA)
    (hcoeff B hB hbB) hdiff
  exact ⟨hh.1,hh.2.1,by simpa only [J, mul_assoc] using hh.2.2⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
