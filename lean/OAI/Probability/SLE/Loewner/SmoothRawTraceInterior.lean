import OAI.Probability.SLE.Loewner.SmoothRawTraceBounds
import OAI.Probability.SLE.Loewner.ReverseLongContraction

namespace OAI

/-! Every positive-time smooth raw tip is in the upper half-plane.
A short reverse interval gives a height bound independent of the
positive height used to approximate the tip. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma smooth_raw_inverse_height_lower (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (haT : a ≤ T)
    (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) (hsmall : L^2*a ≤ 1)
    {y : ℝ} (hy : 0 < y) :
    2*a ≤ (inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)).im^2 := by
  obtain ⟨q,hq0,hqy,hqd,heq⟩ := exists_raw_reverse_trajectory b T
    ((b T : ℂ)+(y : ℂ)*I) (by simpa [upperHalfPlane] using hy)
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
  have hQ (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt q
      (-2/(q s-(u s : ℂ))) (Icc 0 (T : ℝ)) s :=
    (hqd s hs.1).mono Icc_subset_Ici_self
  have hp (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : 0 < (q s).im :=
    hy.trans_le (by simpa using hqy s hs.1)
  have hsub : Icc 0 a ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc_right haT
  have hshort := reverse_loewner_height_lower hL q u (fun s => -b' ((T : ℝ)-s))
    (fun s hs => (hQ s (hsub hs)).mono hsub)
    (fun s hs => (hu s (hsub hs)).mono hsub)
    (fun s hs => by simpa using hb _ (hreflect s (hsub hs)))
    (fun s hs => hp s (hsub hs)) (by simp [hq0,u,driverValue]) hsmall a ⟨ha.le,le_rfl⟩
  have hmono := reverse_height_monotone q u hQ hp
  have hle := hmono ⟨ha.le,haT⟩ ⟨T.coe_nonneg,le_rfl⟩ haT
  rw [heq]
  nlinarith [hp a ⟨ha.le,haT⟩,hp T ⟨T.coe_nonneg,le_rfl⟩]

lemma smooth_raw_trace_height_lower (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (haT : a ≤ T)
    (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) (hsmall : L^2*a ≤ 1) :
    2*a ≤ (trace 1 b T).im^2 := by
  have ht := tendsto_inverseFlow_smooth_trace b T b' hd hL hb
  apply ge_of_tendsto ((Complex.continuous_im.continuousAt.tendsto.comp ht).pow 2)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact smooth_raw_inverse_height_lower b T b' hd hL ha haT hb hsmall hy

theorem smooth_raw_trace_mem_upperHalfPlane (b : Driver) (T : ℝ≥0) (hT : 0 < T)
    (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) :
    trace 1 b T ∈ upperHalfPlane := by
  obtain ⟨a,ha,haT,hs⟩ := exists_smooth_window T (by exact_mod_cast hT) L
  have hl := smooth_raw_trace_height_lower b T b' hd hL ha haT hb hs
  have hn := (smooth_raw_trace_position_bounds b T b' hd hL hb).2.1
  change 0 < (trace 1 b T).im
  nlinarith

end SLEExactGauge.Target

end

end OAI
