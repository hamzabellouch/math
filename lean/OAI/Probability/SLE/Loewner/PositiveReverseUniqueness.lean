import OAI.Probability.SLE.LoewnerReflection

namespace OAI

/-! Ordinary uniqueness after both reverse trajectories have positive height. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

theorem positive_reverse_unique {a T : ℝ} (haT : a ≤ T)
    (q r : ℝ → ℂ) (u : ℝ → ℝ)
    (hqc : ContinuousOn q (Icc a T)) (hrc : ContinuousOn r (Icc a T))
    (hq : ∀ t ∈ Ico a T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Ici t) t)
    (hr : ∀ t ∈ Ico a T, HasDerivWithinAt r
      (-2/(r t-(u t : ℂ))) (Ici t) t)
    (hqp : ∀ t ∈ Icc a T, 0 < (q t).im)
    (hrp : ∀ t ∈ Icc a T, 0 < (r t).im)
    (hinit : q a=r a) : ∀ t ∈ Icc a T, q t=r t := by
  obtain ⟨s,hs,hsm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr haT)
    (Complex.continuous_im.comp_continuousOn hqc)
  obtain ⟨v,hv,hvm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr haT)
    (Complex.continuous_im.comp_continuousOn hrc)
  let η : ℝ := min (q s).im (r v).im
  have hη : 0 < η := lt_min (hqp s hs) (hrp v hv)
  have hQ (t : ℝ) (ht : t ∈ Icc a T) : η ≤ (q t).im :=
    (min_le_left _ _).trans (hsm ht)
  have hR (t : ℝ) (ht : t ∈ Icc a T) : η ≤ (r t).im :=
    (min_le_right _ _).trans (hvm ht)
  have hdQ (t : ℝ) (ht : t ∈ Ico a T) : HasDerivWithinAt q
      (reverseField η (u t) (q t)) (Ici t) t := by
    rw [reverseField,reverseCenter_eq (hQ t (Ico_subset_Icc_self ht))]
    simpa only [div_eq_mul_inv] using hq t ht
  have hdR (t : ℝ) (ht : t ∈ Ico a T) : HasDerivWithinAt r
      (reverseField η (u t) (r t)) (Ici t) t := by
    rw [reverseField,reverseCenter_eq (hR t (Ico_subset_Icc_self ht))]
    simpa only [div_eq_mul_inv] using hr t ht
  have hh := dist_le_of_trajectories_ODE (fun t => reverseField_lipschitz hη (u t))
    hqc hdQ hrc hdR (show dist (q a) (r a) ≤ 0 by rw [hinit]; simp)
  intro t ht
  exact dist_le_zero.mp (by simpa only [zero_mul] using hh t ht)

end SLEExactGauge

end

end OAI
