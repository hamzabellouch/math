import OAI.Analysis.KadisonKastler.ResolventCyclicCuts

namespace OAI

/-! # Vector measures of vectors between two resolvent cuts -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventVectorMeasure_below_cut (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (r : ℝ) (hx : resolventLowerCut R r x = x) :
    ∀ᵐ s ∂resolventVectorMeasure R hR x, s.val < r := by
  let v : ResolventCyclicL2 R hR x :=
    ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ 1
  have hv : resolventCyclicIsometry R hR x v = x := resolventCyclicIsometry_one R hR x
  have he : resolventScalarMultiplier R hR x (resolventCutIndicator R r)
      (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v = v := by
    apply (resolventCyclicIsometry R hR x).injective
    rw [resolventCyclicIsometry_cut, hv, hx]
  have ha := resolventScalarMultiplier_apply_ae R hR x (resolventCutIndicator R r)
    (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v
  rw [he] at ha
  filter_upwards [ha, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (resolventVectorMeasure R hR x) (1 : C(spectrum ℝ R, ℂ))] with s hs hv'
  change v s = 1 at hv'
  rw [hv', mul_one] at hs
  by_contra hn
  simp [resolventCutIndicator, hn] at hs

theorem resolventVectorMeasure_above_cut (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (r : ℝ) (hx : resolventLowerCut R r x = 0) :
    ∀ᵐ s ∂resolventVectorMeasure R hR x, r ≤ s.val := by
  let v : ResolventCyclicL2 R hR x :=
    ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ 1
  have hv : resolventCyclicIsometry R hR x v = x := resolventCyclicIsometry_one R hR x
  have he : resolventScalarMultiplier R hR x (resolventCutIndicator R r)
      (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v = 0 := by
    apply (resolventCyclicIsometry R hR x).injective
    rw [resolventCyclicIsometry_cut, hv, hx, map_zero]
  have ha := resolventScalarMultiplier_apply_ae R hR x (resolventCutIndicator R r)
    (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v
  rw [he] at ha
  filter_upwards [ha, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (resolventVectorMeasure R hR x) (1 : C(spectrum ℝ R, ℂ)),
    Lp.coeFn_zero ℂ 2 (resolventVectorMeasure R hR x)] with s hs hv' hz
  change v s = 1 at hv'
  rw [hv', mul_one, hz] at hs
  by_contra hn
  have hsr : s.val < r := lt_of_not_ge hn
  simp [resolventCutIndicator, hsr] at hs

theorem resolventContinuousCalculus_local_bound
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) (l u : ℝ)
    (hlo : resolventLowerCut R l x = 0) (hhi : resolventLowerCut R u x = x)
    (f : C(spectrum ℝ R, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ s : spectrum ℝ R, l ≤ s.val → s.val < u → ‖f s‖ ≤ C) :
    ‖resolventContinuousCalculus R hR f x‖ ≤ C * ‖x‖ := by
  have ha := (resolventVectorMeasure_above_cut R hR x l hlo).and
    (resolventVectorMeasure_below_cut R hR x u hhi)
  have hi : Integrable (fun s => ‖f s‖^2) (resolventVectorMeasure R hR x) :=
    (f.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle := integral_mono_ae hi (integrable_const (C^2)) (ha.mono fun s hs =>
    pow_le_pow_left₀ (norm_nonneg _) (hb s hs.1 hs.2) 2)
  have hn := resolventContinuousVector_norm_sq R hR x f
  have hone := resolventContinuousVector_norm_sq R hR x 1
  change ‖resolventContinuousCalculus R hR f x‖^2 = _ at hn
  have hunit : resolventContinuousCalculus R hR (1 : C(spectrum ℝ R, ℂ)) x = x := by
    rw [map_one, one_apply_eq_self]
  change ‖resolventContinuousCalculus R hR (1 : C(spectrum ℝ R, ℂ)) x‖^2 = _ at hone
  rw [hunit] at hone
  simp only [ContinuousMap.one_apply, norm_one, one_pow] at hone
  rw [integral_const, smul_eq_mul] at hle
  rw [integral_const, smul_eq_mul, mul_one] at hone
  rw [← hn, ← hone] at hle
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  simpa only [mul_pow, mul_comm] using hle

end

end KadisonKastler

end OAI
