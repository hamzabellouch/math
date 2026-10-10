import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexMultiplierLimit

namespace OAI

/-! Continuous coefficients on the fixed ball, with their actual L²
multipliers and the operator-norm consequence of uniform convergence. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

noncomputable def spectralContinuousCoefficient (R : ℝ) (q : ℝ → ℝ)
    (hq : Continuous q) : SpectralHarmonicWeight R :=
  let hb := isCompact_Icc.bddAbove_image hq.norm.continuousOn
  spectralContinuousWeight R q hq (Classical.choose hb)
    (fun _r hr => Classical.choose_spec hb (mem_image_of_mem _ hr))

theorem spectralContinuousCoefficient_density (R : ℝ) (q : ℝ → ℝ)
    (hq : Continuous q) : (spectralContinuousCoefficient R q hq).density=q := rfl

theorem spectralContinuousCoefficient_bound (R : ℝ) (q : ℝ → ℝ)
    (hq : Continuous q) (r : ℝ) (hr : r ∈ Icc 0 R) :
    ‖q r‖ ≤ (spectralContinuousCoefficient R q hq).bound :=
  Classical.choose_spec (isCompact_Icc.bddAbove_image hq.norm.continuousOn)
    (mem_image_of_mem _ hr)

theorem spectralContinuousMultiplier_tendsto (R : ℝ) (q : ℕ → ℝ → ℝ) (q₀ : ℝ → ℝ)
    (hq : ∀ n, Continuous (q n)) (hq₀ : Continuous q₀)
    (hlim : TendstoUniformlyOn q q₀ atTop (Icc 0 R)) :
    Tendsto (fun n => spectralRadialWeightMultiplier R
      (spectralContinuousCoefficient R (q n) (hq n))) atTop
      (𝓝 (spectralRadialWeightMultiplier R (spectralContinuousCoefficient R q₀ hq₀))) := by
  obtain ⟨δ,hδ,hδ0,hδb⟩ := spectralUniform_error_bound q q₀ hlim (fun n =>
    ⟨(spectralContinuousCoefficient R (q n) (hq n)).bound+
      (spectralContinuousCoefficient R q₀ hq₀).bound, fun r hr =>
        (norm_sub_le _ _).trans (add_le_add
          (spectralContinuousCoefficient_bound R (q n) (hq n) r hr)
          (spectralContinuousCoefficient_bound R q₀ hq₀ r hr))⟩)
  apply spectralRadialWeightMultiplier_tendsto R _ _ δ hδ hδ0
  intro n
  exact radialPressureMeasure_bound R (δ n) _ (hδb n)

end DefocusingNLS

end OAI
