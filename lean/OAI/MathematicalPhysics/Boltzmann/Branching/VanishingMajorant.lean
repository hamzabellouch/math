import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

/-! # Strong L1 convergence under an integrable vanishing majorant -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem tendsto_L1_of_vanishing_majorant
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} {c : ℕ → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hgm : Measurable g) (hgi : Integrable g μ) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hc : Tendsto c atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |f n x| ≤ c n*g x) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0) := by
  have hw : Published.WeakL1Converges μ (fun _ : ℕ => g) g :=
    ⟨hgm,hgi,fun _ _ _ => tendsto_const_nhds⟩
  have hs := hw.vanishing_scalar (Filter.Eventually.of_forall (fun _ => hgi))
    (fun _ => hgn) hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [hb] with n hn
  apply eLpNorm_mono_ae (hfm n)
  filter_upwards [hn,hgn] with x hx hgx
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_nonneg hgx]
  exact hx.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hgx)

end BoltzmannNonuniqueness.Compactness

end

end OAI
