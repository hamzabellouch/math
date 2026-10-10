import OAI.Probability.SLE.Loewner.SmoothReverseContraction

namespace OAI

/-! A short initial contraction, followed by positive-height Grönwall
control, bounds reverse trajectories on any finite time interval. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

lemma reverse_height_monotone {T : ℝ} (q : ℝ → ℂ) (u : ℝ → ℝ)
    (hq : ∀ t ∈ Icc 0 T, HasDerivWithinAt q (-2/(q t-(u t : ℂ))) (Icc 0 T) t)
    (hp : ∀ t ∈ Icc 0 T, 0 < (q t).im) :
    MonotoneOn (fun t => (q t).im) (Icc 0 T) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt (fun s => (q s).im)
      (2*(q t).im/Complex.normSq (q t-(u t : ℂ))) (Icc 0 T) t := by
    have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (hq t ht)
    change HasDerivWithinAt (fun s => (q s).im)
      ((-2/(q t-(u t : ℂ))).im) (Icc 0 T) t at hh
    have he : (-2/(q t-(u t : ℂ))).im =
        2*(q t).im/Complex.normSq (q t-(u t : ℂ)) := by
      simp only [Complex.div_im,Complex.neg_re,Complex.re_ofNat,Complex.neg_im,
        Complex.im_ofNat,neg_zero,zero_mul,Complex.sub_im,Complex.ofReal_im,sub_zero]
      ring
    rwa [he] at hh
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  exact div_nonneg (mul_nonneg (by norm_num) (hp t (interior_subset ht)).le)
    (Complex.normSq_nonneg _)

theorem smooth_reverse_long_distance {T a L : ℝ} (ha : 0 < a) (haT : a ≤ T) (hL : 0 ≤ L)
    (q r : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hq : ∀ t ∈ Icc 0 T, HasDerivWithinAt q (-2/(q t-(u t : ℂ))) (Icc 0 T) t)
    (hr : ∀ t ∈ Icc 0 T, HasDerivWithinAt r (-2/(r t-(u t : ℂ))) (Icc 0 T) t)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (u' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, |u' t| ≤ L)
    (hqp : ∀ t ∈ Icc 0 T, 0 < (q t).im)
    (hrp : ∀ t ∈ Icc 0 T, 0 < (r t).im)
    (hq0 : (q 0).re=u 0) (hr0 : (r 0).re=u 0)
    (hsmall : L^2*a ≤ 1) :
    dist (q T) (r T) ≤ dist (q 0) (r 0)*Real.exp ((4*(Real.sqrt a)⁻¹^2)*(T-a)) := by
  have hsub : Icc 0 a ⊆ Icc 0 T := Icc_subset_Icc_right haT
  have hqd := fun t ht => (hq t (hsub ht)).mono hsub
  have hrd := fun t ht => (hr t (hsub ht)).mono hsub
  have hud := fun t ht => (hu t (hsub ht)).mono hsub
  have hb' := fun t ht => hb t (hsub ht)
  have hqp' := fun t ht => hqp t (hsub ht)
  have hrp' := fun t ht => hrp t (hsub ht)
  have hinit := smooth_reverse_trajectories_contract ha.le hL q r u u'
    hqd hrd hud hb' hqp' hrp' hq0 hr0 hsmall
  have hqa := reverse_loewner_height_lower hL q u u' hqd hud hb' hqp' hq0 hsmall a ⟨ha.le,le_rfl⟩
  have hra := reverse_loewner_height_lower hL r u u' hrd hud hb' hrp' hr0 hsmall a ⟨ha.le,le_rfl⟩
  have hη : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hroot : (Real.sqrt a)^2=a := Real.sq_sqrt ha.le
  have hqa' : Real.sqrt a ≤ (q a).im := by nlinarith [hqp' a ⟨ha.le,le_rfl⟩]
  have hra' : Real.sqrt a ≤ (r a).im := by nlinarith [hrp' a ⟨ha.le,le_rfl⟩]
  have hmQ := reverse_height_monotone q u hq hqp
  have hmR := reverse_height_monotone r u hr hrp
  have hpost : Icc a T ⊆ Icc 0 T := Icc_subset_Icc_left ha.le
  have hQ (t : ℝ) (ht : t ∈ Icc a T) : Real.sqrt a ≤ (q t).im :=
    hqa'.trans (hmQ ⟨ha.le,haT⟩ (hpost ht) ht.1)
  have hR (t : ℝ) (ht : t ∈ Icc a T) : Real.sqrt a ≤ (r t).im :=
    hra'.trans (hmR ⟨ha.le,haT⟩ (hpost ht) ht.1)
  have hdQ (t : ℝ) (ht : t ∈ Ico a T) : HasDerivWithinAt q
      (reverseField (Real.sqrt a) (u t) (q t)) (Ici t) t := by
    rw [reverseField,reverseCenter_eq (hQ t (Ico_subset_Icc_self ht))]
    simpa only [div_eq_mul_inv] using
      hasDerivWithinAt_Ici_of_Icc ht ((hq t (hpost (Ico_subset_Icc_self ht))).mono hpost)
  have hdR (t : ℝ) (ht : t ∈ Ico a T) : HasDerivWithinAt r
      (reverseField (Real.sqrt a) (u t) (r t)) (Ici t) t := by
    rw [reverseField,reverseCenter_eq (hR t (Ico_subset_Icc_self ht))]
    simpa only [div_eq_mul_inv] using
      hasDerivWithinAt_Ici_of_Icc ht ((hr t (hpost (Ico_subset_Icc_self ht))).mono hpost)
  exact dist_le_of_trajectories_ODE (fun t => reverseField_lipschitz hη (u t))
    (fun t ht => (hq t (hpost ht)).continuousWithinAt.mono hpost) hdQ
    (fun t ht => (hr t (hpost ht)).continuousWithinAt.mono hpost) hdR hinit T ⟨haT,le_rfl⟩

end SLEExactGauge

end

end OAI
