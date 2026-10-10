import OAI.Probability.SLE.Loewner.SmoothRawInverse

namespace OAI

/-! Intermediate reverse-time estimates for constructing the raw slit. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma smooth_raw_reverse_estimates (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    (q : ℝ → ℂ)
    (hq : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt q
      (-2/(q t-(driverValue b ((T : ℝ)-t) : ℂ))) (Icc 0 (T : ℝ)) t)
    (hp : ∀ t ∈ Icc 0 (T : ℝ), 0 < (q t).im) (hq0 : (q 0).re=b T)
    (a : ℝ) (ha : a ∈ Icc 0 (T : ℝ)) (hsmall : L^2*a ≤ 1) :
    |(q a).re-driverValue b ((T : ℝ)-a)| ≤ L*a ∧ 2*a ≤ (q a).im^2 := by
  let u (s : ℝ) := driverValue b ((T : ℝ)-s)
  have hreflect (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      (T : ℝ)-s ∈ Icc 0 (T : ℝ) :=
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have hu (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt u
      (-b' ((T : ℝ)-s)) (Icc 0 (T : ℝ)) s := by
    have hi : HasDerivWithinAt (fun t : ℝ => (T : ℝ)-t) (-1) (Icc 0 (T : ℝ)) s := by
      simpa using ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt
    convert! (hd _ (hreflect s hs)).comp s hi hreflect using 1
    simp only [mul_neg,mul_one]
  have hstart : (q 0).re=u 0 := by simpa only [u,sub_zero,driverValue,Real.toNNReal_coe] using hq0
  have hb' : ∀ t ∈ Icc 0 (T : ℝ), |-b' ((T : ℝ)-t)| ≤ L :=
    fun t ht => by simpa only [abs_neg] using hb _ (hreflect t ht)
  refine ⟨(reverse_centered_coordinates hL q u _ hq hu hb' hp hstart).1 a ha,?_⟩
  have hsub : Icc 0 a ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc_right ha.2
  exact reverse_loewner_height_lower hL q u _
    (fun s hs => (hq s (hsub hs)).mono hsub)
    (fun s hs => (hu s (hsub hs)).mono hsub)
    (fun s hs => hb' s (hsub hs)) (fun s hs => hp s (hsub hs))
    hstart hsmall a ⟨ha.1,le_rfl⟩

end SLEExactGauge.Target

end

end OAI
