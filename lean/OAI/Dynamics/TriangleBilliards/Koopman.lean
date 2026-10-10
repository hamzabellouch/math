import OAI.Dynamics.TriangleBilliards.SmoothingApproximation

namespace OAI

universe uA

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-! Hilbert-space analysis of actual measurable measure-preserving flows.
The continuity hypothesis below is only slice-wise almost everywhere and
therefore applies to billiards at each fixed time, despite wall collisions. -/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis

variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

lemma norm_sq_L2 (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := congrArg (RCLike.re (K := ℂ)) (L2.inner_def f f)
  rw [← integral_re] at h
  · simpa only [← norm_sq_eq_re_inner] using h
  · exact L2.integrable_inner f f

variable [TopologicalSpace A] [BorelSpace A]
  [IsFiniteMeasure μ]
  (F : ℝ → A → A) (hm : ∀ t, MeasurePreserving (F t) μ μ)

def koopman (t : ℝ) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (F t) (hm t)

omit [TopologicalSpace A] [BorelSpace A] [IsFiniteMeasure μ] in
lemma coe_koopman (t : ℝ) (f : Lp ℂ 2 μ) :
    (koopman F hm t f : A → ℂ) =ᵐ[μ] (fun x => f (F t x)) :=
  Lp.coeFn_compMeasurePreserving f (hm t)

lemma koopman_bounded_continuous (u : A →ᵇ ℂ) (t : ℝ) :
    (koopman F hm t (BoundedContinuousFunction.toLp 2 μ ℂ u) : A → ℂ) =ᵐ[μ]
      (fun x => u (F t x)) := by
  exact (coe_koopman F hm t _).trans
    ((hm t).quasiMeasurePreserving.ae (BoundedContinuousFunction.coeFn_toLp 2 μ ℂ u))

lemma continuous_koopman_bounded (u : A →ᵇ ℂ)
    (hc : ∀ t, ∀ᵐ x ∂μ, ContinuousAt (fun s => F s x) t) :
    Continuous (fun t => koopman F hm t (BoundedContinuousFunction.toLp 2 μ ℂ u)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let f := BoundedContinuousFunction.toLp 2 μ ℂ u
  have he (s : ℝ) : ‖koopman F hm s f - koopman F hm t f‖ ^ 2 =
      ∫ x, ‖u (F s x) - u (F t x)‖ ^ 2 ∂μ := by
    rw [norm_sq_L2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (koopman F hm s f) (koopman F hm t f),
      koopman_bounded_continuous F hm u s, koopman_bounded_continuous F hm u t] with x hsub hs ht
    simp only [hsub, Pi.sub_apply]
    change ‖(koopman F hm s (BoundedContinuousFunction.toLp 2 μ ℂ u)) x -
      (koopman F hm t (BoundedContinuousFunction.toLp 2 μ ℂ u)) x‖ ^ 2 = _
    rw [hs, ht]
  have hi : Tendsto (fun s : ℝ => ∫ x, ‖u (F s x) - u (F t x)‖ ^ 2 ∂μ)
      (𝓝 t) (𝓝 (∫ x, ‖u (F t x) - u (F t x)‖ ^ 2 ∂μ)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun s =>
        ((((u.continuous.measurable.comp (hm s).measurable).sub
        (u.continuous.measurable.comp (hm t).measurable)).norm.pow_const 2).aestronglyMeasurable)
    · refine ⟨(2 * ‖u‖) ^ 2, Eventually.of_forall fun s => Eventually.of_forall fun x => ?_⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖u (F s x) - u (F t x)‖ ≤ ‖u (F s x)‖ + ‖u (F t x)‖ := norm_sub_le _ _
        _ ≤ 2 * ‖u‖ := by linarith [u.norm_coe_le_norm (F s x), u.norm_coe_le_norm (F t x)]
    · filter_upwards [hc t] with x hx
      exact (((u.continuous.continuousAt.comp hx).sub continuousAt_const).norm.pow 2).tendsto
  have hn : Tendsto (fun s => ‖koopman F hm s f - koopman F hm t f‖)
      (𝓝 t) (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hi
    simpa only [Function.comp_def, ← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), sub_self,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero,
      Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

variable [NormalSpace A] [μ.WeaklyRegular]

lemma continuous_koopman
    (hc : ∀ t, ∀ᵐ x ∂μ, ContinuousAt (fun s => F s x) t) :
    Continuous (fun tf : ℝ × Lp ℂ 2 μ => koopman F hm tf.1 tf.2) := by
  have h : Continuous (fun ft : Lp ℂ 2 μ × ℝ => koopman F hm ft.2 ft.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
      (BoundedContinuousFunction.toLp_denseRange (p := 2) ℂ μ ℂ (by norm_num))
    · rintro _ ⟨u, rfl⟩
      exact continuous_koopman_bounded F hm u hc
    · intro t
      exact (koopman F hm t).isometry.lipschitzWith
  exact h.comp continuous_swap

lemma continuous_koopman_time
    (hc : ∀ t, ∀ᵐ x ∂μ, ContinuousAt (fun s => F s x) t) (f : Lp ℂ 2 μ) :
    Continuous (fun t => koopman F hm t f) :=
  (continuous_koopman F hm hc).comp
    (show Continuous (fun t : ℝ => (t, f)) from continuous_id.prodMk continuous_const)

end TriangularBilliards.Analysis

end
end
end
end

end OAI
