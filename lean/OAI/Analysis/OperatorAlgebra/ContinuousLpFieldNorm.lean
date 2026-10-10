import OAI.Analysis.ModularTheory.LpFaithful

namespace OAI

/-! A continuous operator field is bounded pointwise by its represented L2
operator. The proof tests a constant vector on a small positive-measure interval. -/
noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma continuousLpField_apply_norm_le
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ f, T f =ᵐ[volume] fun t => F t (f t))
    (t₀ : ℝ) (x : H) (hc : ContinuousAt (fun t => F t x) t₀) :
    ‖F t₀ x‖ ≤ ‖T‖ * ‖x‖ := by
  by_contra hn
  have hn' : ‖T‖ * ‖x‖ < ‖F t₀ x‖ := lt_of_not_ge hn
  let c := (‖T‖ * ‖x‖ + ‖F t₀ x‖) / 2
  have hc₁ : ‖T‖ * ‖x‖ < c := by dsimp [c]; linarith
  have hc₂ : c < ‖F t₀ x‖ := by dsimp [c]; linarith
  have hc₀ : 0 ≤ c := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hc₁.le
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc.norm
    (‖F t₀ x‖ - c) (sub_pos.mpr hc₂)
  let l := t₀ - δ / 2
  let r := t₀ + δ / 2
  have hlr : l < r := by dsimp [l, r]; linarith
  have hs : MeasurableSet (Ioo l r) := measurableSet_Ioo
  have hm : volume (Ioo l r) ≠ ⊤ := by simp
  let f : Lp H 2 (volume : Measure ℝ) := indicatorConstLp 2 hs hm x
  let g : Lp ℝ 2 (volume : Measure ℝ) := indicatorConstLp 2 hs hm c
  have he : ‖g‖ ≤ ‖T f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hF f,
      indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hm) (c := x),
      indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hm) (c := c)]
      with t hT hf hg
    change ‖g t‖ ≤ ‖T f t‖
    rw [hg]
    by_cases ht : t ∈ Ioo l r
    · rw [indicator_of_mem ht, Real.norm_eq_abs, abs_of_nonneg hc₀, hT]
      have hft : f t = x := hf.trans (indicator_of_mem ht _)
      rw [hft]
      have htδ : dist t t₀ < δ := by
        rw [Real.dist_eq, abs_lt]
        dsimp [l, r] at ht
        constructor <;> linarith [ht.1, ht.2]
      have hnorm := hd htδ
      rw [Real.dist_eq] at hnorm
      have hbelow := (abs_lt.mp hnorm).1
      linarith
    · rw [indicator_of_notMem ht, norm_zero]
      exact norm_nonneg _
  have he' := he.trans (T.le_opNorm f)
  have hr : 0 < volume.real (Ioo l r) := by
    rw [Real.volume_real_Ioo_of_le hlr.le]
    exact sub_pos.mpr hlr
  have hw : 0 < volume.real (Ioo l r) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    Real.rpow_pos_of_pos hr _
  change ‖indicatorConstLp 2 hs hm c‖ ≤ ‖T‖ * ‖indicatorConstLp 2 hs hm x‖ at he'
  rw [norm_indicatorConstLp (by norm_num) (by norm_num),
    norm_indicatorConstLp (by norm_num) (by norm_num), Real.norm_eq_abs,
    abs_of_nonneg hc₀, ← mul_assoc] at he'
  exact (not_le_of_gt hc₁) ((mul_le_mul_iff_left₀ hw).mp he')

lemma continuousLpField_norm_le
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ f, T f =ᵐ[volume] fun t => F t (f t))
    (t₀ : ℝ) (hc : ∀ x, ContinuousAt (fun t => F t x) t₀) :
    ‖F t₀‖ ≤ ‖T‖ :=
  (F t₀).opNorm_le_bound (norm_nonneg T)
    (fun x => continuousLpField_apply_norm_le T F hF t₀ x (hc x))

end WeakPureInfiniteness

end

end OAI
