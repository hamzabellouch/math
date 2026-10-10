import OAI.Analysis.OperatorAlgebra.ScalarLpCutoffConvergence

namespace OAI

/-! Bounded pointwise convergence of actual scalar multipliers gives strong
operator convergence. Commutation consequently passes to their strong limits.
These lemmas are used to obtain measurable cutoffs from continuous calculus. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace WeakPureInfiniteness

lemma boundedScalarLp_strong
    (b : ℕ → ℝ → ℂ) (a : ℝ → ℂ)
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    (ha : AEStronglyMeasurable a volume) (C : ℝ) (hC : 0 ≤ C)
    (hbn : ∀ n t, ‖b n t‖ ≤ C) (han : ∀ t, ‖a t‖ ≤ C)
    (hlim : ∀ t, Tendsto (fun n => b n t) atTop (𝓝 (a t)))
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => boundedScalarLp volume (b n) (hb n) C (hbn n) f)
      atTop (𝓝 (boundedScalarLp volume a ha C han f)) := by
  let F (n : ℕ) (t : ℝ) := ‖(b n t - a t) * f t‖ ^ 2
  have hbound (n : ℕ) (t : ℝ) : F n t ≤ (2 * C) ^ 2 * ‖f t‖ ^ 2 := by
    have hd : ‖b n t - a t‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith [hbn n t, han t])
    dsimp only [F]
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hC)).mpr hd)
      (sq_nonneg _)
  have hm (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (((hb n).sub ha).mul (Lp.aestronglyMeasurable f)).norm.pow 2
  have hi : Integrable (fun t : ℝ => (2 * C) ^ 2 * ‖f t‖ ^ 2) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)).const_mul _
  have hp (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 0) := by
    have h := (((hlim t).sub_const (a t)).mul_const (f t)).norm.pow 2
    simpa only [sub_self, zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] using h
  have hint : Tendsto (fun n => ∫ t : ℝ, F n t) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (fun t : ℝ => (2 * C) ^ 2 * ‖f t‖ ^ 2) hm hi
      (fun n => ae_of_all _ (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound n t)) (ae_of_all _ hp)
    simpa only [integral_zero] using h
  have heq (n : ℕ) :
      ‖boundedScalarLp volume (b n) (hb n) C (hbn n) f -
        boundedScalarLp volume a ha C han f‖ ^ 2 = ∫ t : ℝ, F n t := by
    rw [scalarLp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (boundedScalarLp volume (b n) (hb n) C (hbn n) f)
      (boundedScalarLp volume a ha C han f),
      boundedScalarLp_ae volume (b n) (hb n) C (hbn n) f,
      boundedScalarLp_ae volume a ha C han f] with t hs hb' ha'
    rw [hs, Pi.sub_apply, hb', ha', ← sub_mul]
  have hsq : Tendsto (fun n => ‖boundedScalarLp volume (b n) (hb n) C (hbn n) f -
      boundedScalarLp volume a ha C han f‖ ^ 2) atTop (𝓝 0) :=
    hint.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hn : Tendsto (fun n => Real.sqrt (‖boundedScalarLp volume (b n) (hb n) C (hbn n) f -
      boundedScalarLp volume a ha C han f‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma scalarLpRepresentation_strong
    (b : ℕ → BoundedContinuousFunction ℝ ℂ) (a : ℝ → ℂ)
    (ha : AEStronglyMeasurable a volume) (C : ℝ) (hC : 0 ≤ C)
    (hbn : ∀ n t, ‖b n t‖ ≤ C) (han : ∀ t, ‖a t‖ ≤ C)
    (hlim : ∀ t, Tendsto (fun n => b n t) atTop (𝓝 (a t)))
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => scalarLpRepresentation volume (b n) f)
      atTop (𝓝 (boundedScalarLp volume a ha C han f)) := by
  have heq (n : ℕ) : boundedScalarLp volume (b n)
      (b n).continuous.aestronglyMeasurable C (hbn n) =
      scalarLpRepresentation volume (b n) := by
    apply ContinuousLinearMap.ext
    intro g
    apply Lp.ext
    filter_upwards [boundedScalarLp_ae volume (b n)
      (b n).continuous.aestronglyMeasurable C (hbn n) g,
      scalarLpMultiplier_ae volume (b n) g] with t hb hc
    exact hb.trans hc.symm
  simpa only [heq] using boundedScalarLp_strong (fun n => b n) a
    (fun n => (b n).continuous.aestronglyMeasurable) ha C hC hbn han hlim f

lemma commute_of_strong_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T U : E →L[ℂ] E) (V : ℕ → E →L[ℂ] E)
    (hc : ∀ n, Commute T (V n))
    (hv : ∀ x, Tendsto (fun n => V n x) atTop (𝓝 (U x))) : Commute T U := by
  apply ContinuousLinearMap.ext
  intro x
  have hleft := T.continuous.continuousAt.tendsto.comp (hv x)
  have hright := hv (T x)
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n =>
    congrArg (fun R : E →L[ℂ] E => R x) (hc n).eq.symm))

end WeakPureInfiniteness

end

end OAI
