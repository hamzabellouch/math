import OAI.NumberTheory.JointDickman.Amplification.RampLocalLaw

namespace OAI

/-! # Regularity of the clipped local-law profile -/

namespace JointDickman

open MeasureTheory Set

open Classical in
theorem clippedIntervalIntegral_eq_clamp (f : ℝ → ℝ) (θ a b t : ℝ) :
    clippedIntervalIntegral f θ a b t = ∫ s in min (b - t) (max θ (a - t))..b - t, f s := by
  unfold clippedIntervalIntegral
  by_cases h : max θ (a - t) ≤ b - t
  · rw [ite_eq_left h, min_eq_right h]
  · rw [ite_eq_right h, min_eq_left (le_of_not_ge h)]
    simp

open Classical in
theorem clippedIntervalIntegral_continuousOn (f : ℝ → ℝ) {lo hi : ℝ}
    (hf : ContinuousOn f (Ici lo)) (a b t : ℝ) :
    ContinuousOn (fun θ => clippedIntervalIntegral f θ a b t) (Icc lo hi) := by
  by_cases hb : lo ≤ b - t
  · have hfi : IntegrableOn f (uIcc lo (b - t)) volume := by
      rw [uIcc_of_le hb]
      exact (hf.mono (fun _ hx => hx.1)).integrableOn_Icc
    have hp := intervalIntegral.continuousOn_primitive_interval_left hfi
    have hc : Continuous (fun θ : ℝ => min (b - t) (max θ (a - t))) :=
      continuous_const.min (continuous_id.max continuous_const)
    have hm : MapsTo (fun θ : ℝ => min (b - t) (max θ (a - t))) (Icc lo hi)
        (uIcc lo (b - t)) := by
      intro θ hθ
      rw [uIcc_of_le hb]
      exact ⟨le_min hb (hθ.1.trans (le_max_left _ _)), min_le_left _ _⟩
    exact (hp.comp hc.continuousOn hm).congr
      (fun θ _ => clippedIntervalIntegral_eq_clamp f θ a b t)
  · apply (continuousOn_const (c := (0 : ℝ))).congr
    intro θ hθ
    unfold clippedIntervalIntegral
    have h : ¬max θ (a - t) ≤ b - t := by
      intro he
      exact hb (hθ.1.trans ((le_max_left _ _).trans he))
    exact ite_eq_right h

open Classical in
theorem scaledClippedProfile_intervalIntegrable (v : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) (a b t : ℝ) :
    IntervalIntegrable
      (fun θ => clippedIntervalIntegral (scaledRoughDensity v z H B) θ a b t)
      volume lo hi := by
  have hc : ContinuousOn (scaledRoughDensity v z H B) (Ici lo) := by
    intro s hs
    exact (hasDerivAt_scaledRoughDensity v z H B (hlo.trans_le hs)).continuousAt.continuousWithinAt
  exact (clippedIntervalIntegral_continuousOn _ hc a b t).intervalIntegrable_of_Icc hlohi

end JointDickman

end OAI
