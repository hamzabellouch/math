import OAI.MathematicalPhysics.Boltzmann.Branching.VanishingMajorant
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance

namespace OAI

section

/-! # Weighted Fatou for entropy production with convergent kernel multipliers -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

theorem lintegral_varying_production_le_liminf
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι}
    [NeBot l] [IsCountablyGenerated l]
    {a b : ι → X → ℝ} {A B : X → ℝ} {w : ι → X → ℝ≥0∞} {W : X → ℝ≥0∞}
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) (hw : ∀ i, Measurable (w i))
    (hA : ∀ᵐ x ∂μ, 0 ≤ A x) (hB : ∀ᵐ x ∂μ, 0 ≤ B x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i => a i x) l (𝓝 (A x)) ∧
      Tendsto (fun i => b i x) l (𝓝 (B x)))
    (hwconv : ∀ᵐ x ∂μ, Tendsto (fun i => w i x) l (𝓝 (W x)))
    (hpos : ∀ᵐ x ∂μ, (∀ᶠ i in l, 0 < a i x) ∧ (∀ᶠ i in l, 0 < b i x)) :
    (∫⁻ x, W x*extendedEntropyProduction (A x) (B x) ∂μ) ≤
      liminf (fun i => ∫⁻ x, w i x*extendedEntropyProduction (a i x) (b i x) ∂μ) l := by
  calc
    _ ≤ ∫⁻ x, liminf (fun i => w i x*extendedEntropyProduction (a i x) (b i x)) l ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hA,hB,hconv,hwconv,hpos] with x hAx hBx hx hwx hpx
      have hs := extendedEntropyProduction_le_liminf hAx hBx hx.1 hx.2 hpx.1 hpx.2
      have hm := ENNReal.le_liminf_mul (u := fun i => w i x)
        (v := fun i => extendedEntropyProduction (a i x) (b i x)) (f := l)
      rw [hwx.liminf_eq] at hm
      exact (mul_le_mul_right hs (W x)).trans hm
    _ ≤ _ := lintegral_liminf_le (fun i => (hw i).mul (measurable_extendedEntropyProduction (ha i) (hb i)))

end BoltzmannNonuniqueness

end

end

section

/-! # Multiplication by a varying uniformly bounded function preserves L1 smallness -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem tendsto_L1_bounded_mul_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f a : ℕ → X → ℝ} (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (ham : ∀ n, AEStronglyMeasurable (a n) μ)
    (hf : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x => a n x*f n x) 1 μ) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n => eLpNorm (fun x => C*f n x) 1 μ) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hf
      (Or.inr (by simp : ‖C‖ₑ ≠ ⊤))
    simpa only [← eLpNorm_const_smul,Pi.smul_def,smul_eq_mul,mul_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [ha] with n hn
  apply eLpNorm_mono_ae ((ham n).mul (hfm n))
  filter_upwards [hn] with x hx
  change |a n x*f n x| ≤ |C*f n x|
  rw [abs_mul,abs_mul,abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
