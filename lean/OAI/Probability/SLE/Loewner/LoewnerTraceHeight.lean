import OAI.Probability.SLE.Loewner.LoewnerDriverBounds

namespace OAI

/-! The deterministic height bound for a capacity-two trace. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.inverse_height_sq_le
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {w : ℂ}
    (hw : w ∈ upperHalfPlane) : (F T w).im^2 ≤ w.im^2+4*T := by
  let q (s : ℝ) := G ((T:ℝ)-s).toNNReal (F T w)
  have hd (s : ℝ) (hs : s ∈ Icc 0 (T:ℝ)) :
      HasDerivWithinAt (fun t => (q t).im^2)
        (4*(q s).im^2/normSq (q s-(U ((T:ℝ)-s).toNNReal : ℂ)))
        (Icc 0 (T:ℝ)) s := by
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s
      (h.reverse_path_unclipped T hw hs)
    change HasDerivWithinAt (fun t => (q t).im)
      ((-2/(q s-(U ((T:ℝ)-s).toNNReal : ℂ))).im) _ _ at hi
    have hh := hi.pow 2
    convert! hh using 1
    simp only [Complex.div_im,Complex.neg_re,Complex.re_ofNat,Complex.neg_im,
      Complex.im_ofNat,neg_zero,zero_mul,Complex.sub_im,Complex.ofReal_im,sub_zero]
    ring
  have hq0 : q 0=w := by
    simp only [q,sub_zero,Real.toNNReal_coe]
    exact h.2.2.2.2.2.2.2.2.1 T w hw
  have hqT : q T=F T w := by
    simp only [q,sub_self,Real.toNNReal_zero]
    exact h.initial_value _ (h.2.2.2.2.2.2.1 T hw).1.1
  have hb := image_le_of_deriv_right_le_deriv_boundary
    (fun s hs => (hd s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hd s ⟨hs.1,hs.2.le⟩))
    (B := fun s => w.im^2+4*s) (B' := fun _ => 4)
    (by simp [hq0]) (by fun_prop)
    (fun s _ => by
      convert (((hasDerivAt_id s).const_mul 4).const_add (w.im^2)).hasDerivWithinAt using 1 <;> simp)
    (fun s hs => ?_) (show (T:ℝ) ∈ Icc 0 (T:ℝ) from ⟨T.coe_nonneg,le_rfl⟩)
  · simpa only [hqT] using hb
  · apply (div_le_iff₀ ?_).mpr
    · simp only [Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,
        Complex.sub_im,Complex.ofReal_im,sub_zero]
      nlinarith [sq_nonneg ((q s).re-U ((T:ℝ)-s).toNNReal)]
    · apply Complex.normSq_pos.mpr
      have hi := h.imag_ge_terminal T (F T w) (h.2.2.2.2.2.2.1 T hw)
        ((T:ℝ)-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩
      rw [h.2.2.2.2.2.2.2.2.1 T w hw] at hi
      intro he
      have him := congrArg Complex.im he
      simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at him
      change w.im ≤ (q s).im at hi
      change 0 < w.im at hw
      linarith

theorem IsCapacityTwoWitness.trace_height_le
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) : (γ T).im ≤ 2*Real.sqrt T := by
  let y (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hy0 : Tendsto y atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hy : Tendsto y atTop (𝓝[>] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨hy0,Eventually.of_forall (fun n => by change 0 < y n; dsimp [y]; positivity)⟩
  have hl := (Complex.continuous_im.continuousAt.tendsto.comp
    ((h.2.2.2.2.2.2.2.2.2.2.2.2 T).comp hy)).pow 2
  have hr := (hy0.pow 2).add_const (4*(T:ℝ))
  have hb : (γ T).im^2 ≤ 4*(T:ℝ) := by
    apply le_of_tendsto_of_tendsto hl (by simpa using hr)
    apply Eventually.of_forall
    intro n
    have hh := h.inverse_height_sq_le T
      (w := (U T:ℂ)+(y n:ℂ)*I) (by
        change 0 < ((U T:ℂ)+(y n:ℂ)*I).im
        simpa using (show 0 < y n by dsimp [y]; positivity))
    simpa using hh
  have hs := Real.sq_sqrt T.coe_nonneg
  nlinarith [Real.sqrt_nonneg (T:ℝ)]

end SLEExactGauge

end

end OAI
