import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter TopologicalSpace

namespace Problem367

theorem ae_eq_of_dense_evaluations
    {Ω T E I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [TopologicalSpace E] [T2Space E] [Countable I]
    (e : I → T) (he : DenseRange e) {f g : Ω → T → E}
    (hf : ∀ᵐ ω ∂μ, Continuous (f ω)) (hg : ∀ᵐ ω ∂μ, Continuous (g ω))
    (hfg : ∀ i, ∀ᵐ ω ∂μ, f ω (e i) = g ω (e i)) : f =ᵐ[μ] g := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, f ω (e i) = g ω (e i) :=
    ae_all_iff.mpr hfg
  filter_upwards [hf, hg, hall] with ω hfω hgω hω
  exact he.equalizer hfω hgω (funext hω)

theorem ae_eq_of_continuous_of_evaluation_ae_eq
    {Ω T E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    [TopologicalSpace E] [T2Space E] {f g : Ω → T → E}
    (hf : ∀ᵐ ω ∂μ, Continuous (f ω)) (hg : ∀ᵐ ω ∂μ, Continuous (g ω))
    (hfg : ∀ t, ∀ᵐ ω ∂μ, f ω t = g ω t) : f =ᵐ[μ] g := by
  exact ae_eq_of_dense_evaluations (TopologicalSpace.denseSeq T)
    (TopologicalSpace.denseRange_denseSeq T) hf hg (fun _ => hfg _)

theorem ae_eq_of_integral_sq_sub_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hInt : Integrable (fun ω => (f ω - g ω) ^ 2) μ)
    (hzero : (∫ ω, (f ω - g ω) ^ 2 ∂μ) = 0) : f =ᵐ[μ] g := by
  have h := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (f ω - g ω))
    hInt).mp hzero
  filter_upwards [h] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

theorem ae_eq_of_continuous_of_integral_sq_sub_eq_zero
    {Ω T : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T] {f g : Ω → T → ℝ}
    (hf : ∀ᵐ ω ∂μ, Continuous (f ω)) (hg : ∀ᵐ ω ∂μ, Continuous (g ω))
    (hInt : ∀ t, Integrable (fun ω => (f ω t - g ω t) ^ 2) μ)
    (hzero : ∀ t, (∫ ω, (f ω t - g ω t) ^ 2 ∂μ) = 0) : f =ᵐ[μ] g := by
  apply ae_eq_of_continuous_of_evaluation_ae_eq hf hg
  exact fun t => ae_eq_of_integral_sq_sub_eq_zero (hInt t) (hzero t)

theorem ae_eq_array_of_continuous_of_integral_sq_sub_eq_zero
    {Ω V T : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Countable V]
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    {f g : Ω → V → T → ℝ}
    (hf : ∀ v, ∀ᵐ ω ∂μ, Continuous (f ω v))
    (hg : ∀ v, ∀ᵐ ω ∂μ, Continuous (g ω v))
    (hInt : ∀ v t, Integrable (fun ω => (f ω v t - g ω v t) ^ 2) μ)
    (hzero : ∀ v t, (∫ ω, (f ω v t - g ω v t) ^ 2 ∂μ) = 0) : f =ᵐ[μ] g := by
  have h : ∀ v, ∀ᵐ ω ∂μ, f ω v = g ω v := fun v =>
    ae_eq_of_continuous_of_integral_sq_sub_eq_zero (hf v) (hg v) (hInt v) (hzero v)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact funext hω

end Problem367

end

end OAI
