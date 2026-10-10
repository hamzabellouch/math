import OAI.Probability.SLE.Loewner.SmoothRawInverse

namespace OAI

/-! The elementary upper height bound for reverse trajectories applies
before a trace or a geometric hull is available. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma reverse_height_square_le {T : ℝ} (hT : 0 ≤ T)
    (q : ℝ → ℂ) (u : ℝ → ℝ)
    (hd : ∀ s ∈ Icc 0 T, HasDerivWithinAt q (-2/(q s-(u s : ℂ))) (Icc 0 T) s)
    (hp : ∀ s ∈ Icc 0 T, 0 < (q s).im) :
    (q T).im^2 ≤ (q 0).im^2+4*T := by
  have hsq (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivWithinAt (fun t => (q t).im^2)
        (4*(q s).im^2/normSq (q s-(u s : ℂ))) (Icc 0 T) s := by
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s (hd s hs)
    change HasDerivWithinAt (fun t => (q t).im)
      ((-2/(q s-(u s : ℂ))).im) _ _ at hi
    convert! hi.pow 2 using 1
    simp only [Complex.div_im,Complex.neg_re,Complex.re_ofNat,Complex.neg_im,
      Complex.im_ofNat,neg_zero,zero_mul,Complex.sub_im,Complex.ofReal_im,sub_zero]
    ring
  apply image_le_of_deriv_right_le_deriv_boundary
    (fun s hs => (hsq s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hsq s ⟨hs.1,hs.2.le⟩))
    (B := fun s => (q 0).im^2+4*s) (B' := fun _ => 4)
    (by simp) (by fun_prop)
    (fun s _ => by
      convert (((hasDerivAt_id s).const_mul 4).const_add ((q 0).im^2)).hasDerivWithinAt using 1 <;> simp)
    (fun s hs => ?_) ⟨hT,le_rfl⟩
  apply (div_le_iff₀ ?_).mpr
  · simp only [Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,
      Complex.sub_im,Complex.ofReal_im,sub_zero]
    nlinarith [sq_nonneg ((q s).re-u s)]
  · apply Complex.normSq_pos.mpr
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact (hp s (Ico_subset_Icc_self hs)).ne' hi

namespace Target

lemma raw_inverse_height_square_le (b : Driver) (T : ℝ≥0) (w : ℂ)
    (hw : w ∈ upperHalfPlane) : (inverseFlow 1 b T w).im^2 ≤ w.im^2+4*T := by
  obtain ⟨q,hq0,hheight,hd,he⟩ := exists_raw_reverse_trajectory b T w hw
  rw [he,← hq0]
  exact reverse_height_square_le T.coe_nonneg q (fun s => driverValue b ((T : ℝ)-s))
    (fun s hs => (hd s hs.1).mono Icc_subset_Ici_self)
    (fun s hs => hw.trans_le (hheight s hs.1))

end Target
end SLEExactGauge

end

end OAI
