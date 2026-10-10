import OAI.Analysis.OperatorAlgebra.VectorLpMultiplier

namespace OAI

/-! Strong convergence of scalar multipliers on vector-valued L². This is
used to put frequency cutoffs and Gaussian regularizers into the actual
modular core. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma vectorLp_norm_sq_integral (f : Lp H 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ t : ℝ, ‖f t‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = (inner ℂ f f).re := (inner_self_eq_norm_sq (𝕜 := ℂ) f).symm
    _ = ∫ t : ℝ, (inner ℂ (f t) (f t)).re := by
      rw [L2.inner_def]
      exact (integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = ∫ t : ℝ, ‖f t‖ ^ 2 := by
      congr 1
      funext t
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (f t)

omit [CompleteSpace H] in
lemma boundedVectorLp_strong
    (b : ℕ → ℝ → ℂ) (a : ℝ → ℂ)
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    (ha : AEStronglyMeasurable a volume) (C : ℝ) (_hC : 0 ≤ C)
    (hbn : ∀ n t, ‖b n t‖ ≤ C) (han : ∀ t, ‖a t‖ ≤ C)
    (hlim : ∀ t, Tendsto (fun n => b n t) atTop (𝓝 (a t)))
    (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => boundedVectorLp volume (b n) (hb n) C (hbn n) f)
      atTop (𝓝 (boundedVectorLp volume a ha C han f)) := by
  let F (n : ℕ) (t : ℝ) := ‖(b n t - a t) • f t‖ ^ 2
  have hbound (n : ℕ) (t : ℝ) : F n t ≤ (2 * C) ^ 2 * ‖f t‖ ^ 2 := by
    have hd : ‖b n t - a t‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith [hbn n t, han t])
    dsimp only [F]
    rw [norm_smul, mul_pow]
    gcongr
  have hm (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (((hb n).sub ha).smul (Lp.aestronglyMeasurable f)).norm.pow 2
  have hi : Integrable (fun t : ℝ => (2 * C) ^ 2 * ‖f t‖ ^ 2) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)).const_mul _
  have hp (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 0) := by
    have h := (((hlim t).sub_const (a t)).smul_const (f t)).norm.pow 2
    simpa only [sub_self, zero_smul, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] using h
  have hint : Tendsto (fun n => ∫ t : ℝ, F n t) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (fun t : ℝ => (2 * C) ^ 2 * ‖f t‖ ^ 2) hm hi
      (fun n => ae_of_all _ (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound n t)) (ae_of_all _ hp)
    simpa only [integral_zero] using h
  have heq (n : ℕ) :
      ‖boundedVectorLp volume (b n) (hb n) C (hbn n) f -
        boundedVectorLp volume a ha C han f‖ ^ 2 = ∫ t : ℝ, F n t := by
    rw [vectorLp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (boundedVectorLp volume (b n) (hb n) C (hbn n) f)
      (boundedVectorLp volume a ha C han f),
      boundedVectorLp_ae volume (b n) (hb n) C (hbn n) f,
      boundedVectorLp_ae volume a ha C han f] with t hs hb' ha'
    rw [hs, Pi.sub_apply, hb', ha', ← sub_smul]
  have hsq : Tendsto (fun n => ‖boundedVectorLp volume (b n) (hb n) C (hbn n) f -
      boundedVectorLp volume a ha C han f‖ ^ 2) atTop (𝓝 0) :=
    hint.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hn : Tendsto (fun n => Real.sqrt (‖boundedVectorLp volume (b n) (hb n) C (hbn n) f -
      boundedVectorLp volume a ha C han f‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma vectorLpRepresentation_strong
    (b : ℕ → BoundedContinuousFunction ℝ ℂ) (a : ℝ → ℂ)
    (ha : AEStronglyMeasurable a volume) (C : ℝ) (hC : 0 ≤ C)
    (hbn : ∀ n t, ‖b n t‖ ≤ C) (han : ∀ t, ‖a t‖ ≤ C)
    (hlim : ∀ t, Tendsto (fun n => b n t) atTop (𝓝 (a t)))
    (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => vectorLpRepresentation volume (b n) f)
      atTop (𝓝 (boundedVectorLp volume a ha C han f)) := by
  have heq (n : ℕ) : boundedVectorLp (H := H) volume (b n)
      (b n).continuous.aestronglyMeasurable C (hbn n) =
      vectorLpRepresentation (H := H) volume (b n) := by
    apply ContinuousLinearMap.ext
    intro g
    apply Lp.ext
    filter_upwards [boundedVectorLp_ae volume (b n)
      (b n).continuous.aestronglyMeasurable C (hbn n) g,
      vectorLpMultiplier_ae volume (b n) g] with t hb hc
    exact hb.trans hc.symm
  simpa only [heq] using boundedVectorLp_strong (fun n => b n) a
    (fun n => (b n).continuous.aestronglyMeasurable) ha C hC hbn han hlim f

end WeakPureInfiniteness

end

end OAI
