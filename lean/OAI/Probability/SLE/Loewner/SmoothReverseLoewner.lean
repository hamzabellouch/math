import OAI.Probability.SLE.Loewner.ReverseSmoothBounds

namespace OAI

/-! Uniform height estimates for reverse Loewner trajectories driven by a
function with bounded derivative. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma reverse_centered_coordinates {T L : ℝ} (hL : 0 ≤ L)
    (q : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hq : ∀ t ∈ Icc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Icc 0 T) t)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (u' t) (Icc 0 T) t)
    (hbound : ∀ t ∈ Icc 0 T, |u' t| ≤ L)
    (hpos : ∀ t ∈ Icc 0 T, 0 < (q t).im)
    (hstart : (q 0).re=u 0) :
    (∀ t ∈ Icc 0 T, |(q t).re-u t| ≤ L*t) ∧
    (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (q s).im)
      (2*(q t).im/(((q t).re-u t)^2+(q t).im^2)) (Icc 0 T) t) := by
  let D (t : ℝ) := ((q t).re-u t)^2+(q t).im^2
  have hD (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < D t := by
    have hp := hpos t ht
    dsimp [D]
    positivity
  have hre (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt
      (fun s => (q s).re-u s) (-2*((q t).re-u t)/D t-u' t) (Icc 0 T) t := by
    have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hq t ht)).sub (hu t ht)
    change HasDerivWithinAt (fun s => (q s).re-u s)
      ((-2/(q t-(u t : ℂ))).re-u' t) (Icc 0 T) t at hd
    have he : (-2/(q t-(u t : ℂ))).re = -2*((q t).re-u t)/D t := by
      simp [D,Complex.div_re,Complex.normSq_apply,pow_two]
    rwa [he] at hd
  refine ⟨damped_real_abs_barrier hL (fun s => (q s).re-u s) (fun s => -u' s) D
    (sub_eq_zero.mpr hstart) (fun t ht => ?_) hD (fun t ht => by simpa using hbound t ht),?_⟩
  · convert hre t ht using 1
  · intro t ht
    have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (hq t ht)
    change HasDerivWithinAt (fun s => (q s).im)
      ((-2/(q t-(u t : ℂ))).im) (Icc 0 T) t at hd
    have he : (-2/(q t-(u t : ℂ))).im =
        2*(q t).im/(((q t).re-u t)^2+(q t).im^2) := by
      simp [Complex.div_im,Complex.normSq_apply,pow_two]
      ring
    rwa [he] at hd

theorem reverse_loewner_height_lower {T L : ℝ} (hL : 0 ≤ L)
    (q : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hq : ∀ t ∈ Icc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Icc 0 T) t)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (u' t) (Icc 0 T) t)
    (hbound : ∀ t ∈ Icc 0 T, |u' t| ≤ L)
    (hpos : ∀ t ∈ Icc 0 T, 0 < (q t).im)
    (hstart : (q 0).re=u 0) (hsmall : L^2*T ≤ 1) :
    ∀ t ∈ Icc 0 T, 2*t ≤ (q t).im^2 := by
  obtain ⟨hx,hy⟩ := reverse_centered_coordinates hL q u u' hq hu hbound hpos hstart
  exact reverse_height_square_barrier (fun s => (q s).re-u s) (fun s => (q s).im)
    hpos hy hx (fun t ht =>
      (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg L)).trans hsmall)

theorem IsCapacityTwoWitness.inverse_tip_height_lower
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (U' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => U s.toNNReal)
      (U' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ t ∈ Icc 0 (T : ℝ), |U' t| ≤ L)
    (hsmall : L^2*(T : ℝ) ≤ 1) {y : ℝ} (hy : 0 < y) :
    2*(T : ℝ) ≤ (F T ((U T : ℂ)+(y : ℂ)*I)).im^2 := by
  let w : ℂ := (U T : ℂ)+(y : ℂ)*I
  have hw : w ∈ upperHalfPlane := by simpa [w,upperHalfPlane] using hy
  let q (s : ℝ) := G ((T : ℝ)-s).toNNReal (F T w)
  let u (s : ℝ) := U ((T : ℝ)-s).toNNReal
  have hreflect (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      (T : ℝ)-s ∈ Icc 0 (T : ℝ) := ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have hu (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt u
      (-U' ((T : ℝ)-s)) (Icc 0 (T : ℝ)) s := by
    have hi : HasDerivWithinAt (fun r : ℝ => (T : ℝ)-r) (-1)
        (Icc 0 (T : ℝ)) s := by
      simpa using ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt
    simpa only [Function.comp_def,mul_neg,mul_one] using
      (hd _ (hreflect s hs)).comp s hi hreflect
  have hq0 : q 0=w := by
    simp only [q,sub_zero,Real.toNNReal_coe]
    exact h.2.2.2.2.2.2.2.2.1 T w hw
  have hqT : q T=F T w := by
    simp only [q,sub_self,Real.toNNReal_zero]
    exact h.initial_value _ (h.2.2.2.2.2.2.1 T hw).1.1
  have hh := reverse_loewner_height_lower hL q u
    (fun s => -U' ((T : ℝ)-s)) (fun s hs => h.reverse_path_unclipped T hw hs) hu
    (fun s hs => by simpa using hbound _ (hreflect s hs))
    (fun s hs => h.imag_positive _ _ (survivingDomain_antitone γ
      ((Real.toNNReal_le_iff_le_coe).mpr (hreflect s hs).2) (h.2.2.2.2.2.2.1 T hw)))
    (by simp [hq0,w,u]) hsmall T ⟨T.coe_nonneg,le_rfl⟩
  simpa only [hqT,w] using hh

theorem IsCapacityTwoWitness.smooth_trace_height_lower
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (U' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => U s.toNNReal)
      (U' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ t ∈ Icc 0 (T : ℝ), |U' t| ≤ L)
    (hsmall : L^2*(T : ℝ) ≤ 1) :
    2*(T : ℝ) ≤ (γ T).im^2 := by
  have hl := ((Complex.continuous_im.continuousAt.tendsto.comp
    (h.2.2.2.2.2.2.2.2.2.2.2.2 T)).pow 2)
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact h.inverse_tip_height_lower T U' hd hL hbound hsmall hy

end SLEExactGauge

end

end OAI
