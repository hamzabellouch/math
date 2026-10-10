import OAI.Analysis.KadisonKastler.MinimalSpatialImplementer

namespace OAI

/-! # Lower semicontinuity of vector distances in the weak operator topology -/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wot_vector_sqDistance_lowerSemicontinuous (ξ η : H) :
    LowerSemicontinuous (fun T : H →WOT[ℂ] H => ‖T ξ - η‖ ^ 2) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  change IsClosed {T : H →WOT[ℂ] H | ‖T ξ - η‖ ^ 2 ≤ r}
  by_cases hr : 0 ≤ r
  · have he : {T : H →WOT[ℂ] H | ‖T ξ - η‖ ^ 2 ≤ r} =
        {T | ∀ ζ : H, ‖inner ℂ ζ (T ξ - η)‖ ^ 2 ≤ r * ‖ζ‖ ^ 2} := by
      ext T
      constructor
      · intro h ζ
        calc
          ‖inner ℂ ζ (T ξ - η)‖ ^ 2 ≤ (‖ζ‖ * ‖T ξ - η‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
          _ ≤ r * ‖ζ‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ‖ζ‖)]
      · intro h
        have hh := h (T ξ - η)
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)] at hh
        change ‖T ξ - η‖ ^ 2 ≤ r
        by_cases hn : ‖T ξ - η‖ = 0
        · simpa only [hn, zero_pow (by decide : 2 ≠ 0)] using hr
        · apply (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero hn)).mp
          simpa only [pow_two, mul_comm] using hh
    rw [he]
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro ζ
    have hc : Continuous (fun T : H →WOT[ℂ] H => inner ℂ ζ (T ξ)) :=
      continuous_inner_apply continuous_id ξ ζ
    have hn : Continuous (fun T : H →WOT[ℂ] H =>
        ‖inner ℂ ζ (T ξ - η)‖) := by
      simpa only [inner_sub_right, Pi.sub_apply] using (hc.sub continuous_const).norm
    have hs : Continuous (fun T : H →WOT[ℂ] H =>
        ‖inner ℂ ζ (T ξ - η)‖ ^ 2) := by
      convert hn.mul hn using 1
      ext T
      simp only [Pi.mul_apply, pow_two]
    exact isClosed_le hs continuous_const
  · have he : {T : H →WOT[ℂ] H | ‖T ξ - η‖ ^ 2 ≤ r} = ∅ := by
      ext T
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hr) (sq_nonneg _))
    rw [he]
    exact isClosed_empty

end

end KadisonKastler

end OAI
