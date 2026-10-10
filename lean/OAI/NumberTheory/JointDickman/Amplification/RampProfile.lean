import OAI.NumberTheory.JointDickman.Amplification.RampDensity

namespace OAI

/-! # Identifying the smoothed local-law profile -/

namespace JointDickman

open MeasureTheory Set
open scoped NNReal

open Classical in
theorem clippedIntervalIntegral_congr_above (f g : ℝ → ℝ) {lo θ : ℝ}
    (hθ : lo ≤ θ) (hfg : ∀ s ∈ Ici lo, f s = g s) (a b t : ℝ) :
    clippedIntervalIntegral f θ a b t = clippedIntervalIntegral g θ a b t := by
  unfold clippedIntervalIntegral
  split_ifs with hab
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact hfg s (hθ.trans ((le_max_left _ _).trans hs.1))
  · rfl

open Classical in
theorem rampIntervalIntegral_eq_rampDensity (f : ℝ → ℝ) {lo hi : ℝ} {L : ℝ≥0}
    (hlohi : lo < hi) (hLip : LipschitzOnWith L f (Ici lo))
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    rampIntervalIntegral f lo hi a b t =
      ∫ x in a..b, rampDensity f lo hi (x - t) := by
  let g : ℝ → ℝ := fun s => f (max lo s)
  have hg : Continuous g := (clampedDensity_lipschitz f hLip).continuous
  have heq : rampIntervalIntegral f lo hi a b t =
      rampIntervalIntegral g lo hi (a - t) (b - t) 0 := by
    unfold rampIntervalIntegral
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hlohi.le] at hθ
    have hc := clippedIntervalIntegral_congr_above f g hθ.1
      (fun s hs => by simp only [g, max_eq_right (Set.mem_Ici.mp hs)]) a b t
    simpa only [clippedIntervalIntegral, sub_zero] using hc
  rw [heq, rampIntervalIntegral_eq_density g hg hlohi (sub_le_sub_right hab t)]
  rw [intervalIntegral.integral_comp_sub_right]
  rfl

end JointDickman

end OAI
