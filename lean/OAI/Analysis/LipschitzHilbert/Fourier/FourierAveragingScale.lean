import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingMixture

namespace OAI

/-!
# The source scales for the near-uniform averaging probability

Write `h = G^(-1/16)`. The expansion padding is `H*h/2` and the
physical kernel scale is `H*h²`. The resulting loss is exactly
`h + 4*M*h²`, hence at most a fixed constant times `h`.
-/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

open PhaseCombinatorics

theorem averaging_loss_at_source_scales {H h M : ℝ} (hH : 0 < H) (hh : 0 < h) :
    2 * (H * h / 2) / H + (H * h ^ 2) ^ 2 * M / (H * h / 2) ^ 2 =
      h + 4 * M * h ^ 2 := by
  field_simp [hH.ne', hh.ne']
  ring

theorem averaging_source_loss_bound {h M : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hM : 0 ≤ M) :
    h + 4 * M * h ^ 2 ≤ (1 + 4 * M) * h := by
  have hs : h ^ 2 ≤ h := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * M)]

/-- A universal averaging constant and a genuine probability remainder at
every source scale. This discharges the probability-mixture existence
obligation used by the graph prediction argument. -/
theorem exists_source_scale_averaging_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b h : ℝ), a < b → 0 < h → h ≤ 1 → C * h < 1 / 2 →
      ∃ (η : ℝ) (τ : Measure ℝ), 0 < η ∧ η ≤ C * h ∧ η < 1 / 2 ∧
        IsProbabilityMeasure τ ∧
        FourierGap (predictionMixture (intervalProbability a b) τ η)
          (1 / ((b - a) * h ^ 2)) := by
  obtain ⟨μ, hprob, hgap, hmoment⟩ := exists_fixed_fourier_averaging_kernel
  let M := ∫ t : ℝ, t ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  refine ⟨1 + 4 * M, by linarith, ?_⟩
  intro a b h hab hh0 hh1 hsmall
  have hH : 0 < b - a := sub_pos.mpr hab
  have hpad : 0 < (b - a) * h / 2 := by positivity
  have hscale : 0 < (b - a) * h ^ 2 := by positivity
  let η := h + 4 * M * h ^ 2
  have hηbound : η ≤ (1 + 4 * M) * h := averaging_source_loss_bound hh0.le hh1 hM
  have hηsmall : η < 1 / 2 := hηbound.trans_lt hsmall
  have hformula := averaging_loss_at_source_scales (M := M) hH hh0
  have hsmall' : 2 * ((b - a) * h / 2) / (b - a) +
      ((b - a) * h ^ 2) ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / ((b - a) * h / 2) ^ 2 < 1 := by
    rw [hformula]
    exact hηsmall.trans (by norm_num)
  obtain ⟨hη0, _, τ, hτ, _, hν⟩ := interval_fourier_mixture μ hmoment hab hpad hscale hgap hsmall'
  rw [hformula] at hη0 hν
  exact ⟨η, τ, hη0, hηbound, hηsmall, hτ, hν⟩

theorem fourierGap_mono (μ : Measure ℝ) {gap gap' : ℝ}
    (hν : FourierGap μ gap) (hgap : gap ≤ gap') : FourierGap μ gap' := by
  intro s hs
  exact hν s (by linarith)

/-- The manuscript's powers of `G`, with a universal error coefficient. -/
theorem exists_power_scale_averaging_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b G : ℝ), a < b → 1 ≤ G →
      C * G ^ (-(1 / 16 : ℝ)) < 1 / 2 →
      ∃ (η : ℝ) (τ : Measure ℝ), 0 < η ∧ η ≤ C * G ^ (-(1 / 16 : ℝ)) ∧
        η < 1 / 2 ∧ IsProbabilityMeasure τ ∧
        FourierGap (predictionMixture (intervalProbability a b) τ η)
          (1 / ((b - a) * G ^ (-(1 / 8 : ℝ)))) := by
  obtain ⟨C, hC, hmain⟩ := exists_source_scale_averaging_constant
  refine ⟨C, hC, ?_⟩
  intro a b G hab hG hsmall
  have hG0 : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hh0 : 0 < G ^ (-(1 / 16 : ℝ)) := Real.rpow_pos_of_pos hG0 _
  have hh1 : G ^ (-(1 / 16 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  obtain ⟨η, τ, hη0, hηC, hηhalf, hτ, hν⟩ := hmain a b _ hab hh0 hh1 hsmall
  have hsquare : (G ^ (-(1 / 16 : ℝ))) ^ 2 = G ^ (-(1 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hG0.le]
    norm_num
  rw [hsquare] at hν
  exact ⟨η, τ, hη0, hηC, hηhalf, hτ, hν⟩

end LipschitzHilbert

end

end OAI
