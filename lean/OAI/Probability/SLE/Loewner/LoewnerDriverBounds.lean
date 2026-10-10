import OAI.Probability.SLE.LoewnerReflection

namespace OAI

/-! Deterministic confinement from the driving function, obtained from the
reverse Loewner equation before taking the actual boundary trace limit. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.reverse_path_unclipped
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {w : ℂ}
    (hw : w ∈ upperHalfPlane) {s : ℝ} (hs : s ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun t : ℝ => G ((T : ℝ) - t).toNNReal (F T w))
      (-2 / (G ((T : ℝ) - s).toNNReal (F T w) - (U ((T : ℝ) - s).toNNReal : ℂ)))
      (Icc 0 (T : ℝ)) s := by
  have hz := h.2.2.2.2.2.2.1 T hw
  have hi := h.imag_ge_terminal T (F T w) hz ((T : ℝ) - s)
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [h.2.2.2.2.2.2.2.2.1 T w hw] at hi
  simpa only [reverseField, reverseCenter_eq hi, div_eq_mul_inv] using
    h.reverse_path_derivative T w hw le_rfl s hs

lemma IsCapacityTwoWitness.inverse_re_le
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {w : ℂ}
    (hw : w ∈ upperHalfPlane) {M : ℝ}
    (hwM : w.re ≤ M) (hU : ∀ t ∈ Icc 0 T, U t ≤ M) : (F T w).re ≤ M := by
  let q (s : ℝ) := G ((T : ℝ) - s).toNNReal (F T w)
  have hq (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) := h.reverse_path_unclipped T hw hs
  have hq0 : q 0 = w := by
    simp only [q, sub_zero, Real.toNNReal_coe]
    exact h.2.2.2.2.2.2.2.2.1 T w hw
  have hqT : q T = F T w := by
    simp only [q, sub_self, Real.toNNReal_zero]
    exact h.initial_value _ (h.2.2.2.2.2.2.1 T hw).1.1
  apply le_of_forall_pos_le_add
  intro ε hε
  have hr (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      HasDerivWithinAt (fun t => (q t).re)
        ((-2 * ((q s).re - U ((T : ℝ) - s).toNNReal)) /
          normSq (q s - (U ((T : ℝ) - s).toNNReal : ℂ))) (Icc 0 (T : ℝ)) s := by
    have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s (hq s hs)
    change HasDerivWithinAt (fun t => (q t).re)
      ((-2 / (q s - (U ((T : ℝ) - s).toNNReal : ℂ))).re) _ _ at hd
    simpa only [Function.comp_def, Complex.div_re, Complex.neg_re, Complex.re_ofNat,
      Complex.neg_im, Complex.im_ofNat, neg_zero, zero_mul, zero_div, add_zero,
      Complex.sub_re, Complex.ofReal_re] using hd
  have hc : ContinuousOn (fun t => (q t).re) (Icc 0 (T : ℝ)) :=
    fun s hs => (hr s hs).continuousWithinAt
  have hbound := image_le_of_deriv_right_lt_deriv_boundary hc
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hr s ⟨hs.1,hs.2.le⟩))
    (B := fun _ => M + ε) (B' := fun _ => 0)
    (by rw [hq0]; linarith)
    (fun _ => hasDerivAt_const _ _) (fun s hs he => ?_)
    (show (T : ℝ) ∈ Icc 0 (T : ℝ) from ⟨T.coe_nonneg,le_rfl⟩)
  · simpa only [hqT] using hbound
  · have ht : ((T : ℝ)-s).toNNReal ∈ Icc 0 T := by
      refine ⟨zero_le,?_⟩
      exact_mod_cast (show (((T : ℝ)-s).toNNReal : ℝ) ≤ T by
        rw [Real.coe_toNNReal _ (by linarith [hs.2])]; linarith [hs.1])
    have him : 0 < (q s).im := h.imag_positive _ _
      (survivingDomain_antitone γ ht.2 (h.2.2.2.2.2.2.1 T hw))
    have hne : q s - (U ((T : ℝ)-s).toNNReal : ℂ) ≠ 0 := by
      intro hn
      have hh := congrArg Complex.im hn
      simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hh
      exact him.ne' hh
    apply div_neg_of_neg_of_pos _ (Complex.normSq_pos.mpr hne)
    rw [he]
    nlinarith [hU _ ht]

lemma IsCapacityTwoWitness.trace_re_le
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {M : ℝ}
    (hU : ∀ t ∈ Icc 0 T, U t ≤ M) : (γ T).re ≤ M := by
  have hl := Complex.continuous_re.continuousAt.tendsto.comp
    (h.2.2.2.2.2.2.2.2.2.2.2.2 T)
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with y hy
  apply h.inverse_re_le T (show (U T : ℂ)+(y:ℂ)*I ∈ upperHalfPlane by
    simpa [upperHalfPlane] using hy) (by simpa using hU T ⟨zero_le,le_rfl⟩) hU

lemma IsCapacityTwoWitness.trace_abs_re_le
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {M : ℝ}
    (hU : ∀ t ∈ Icc 0 T, |U t| ≤ M) : |(γ T).re| ≤ M := by
  apply abs_le.mpr
  refine ⟨?_,h.trace_re_le T (fun t ht => (le_abs_self _).trans (hU t ht))⟩
  have hh := h.mirror.trace_re_le T (fun t ht => (neg_le_abs _).trans (hU t ht))
  simpa only [Function.comp_apply,loewnerMirror_re,neg_le] using hh

end SLEExactGauge

end

end OAI
