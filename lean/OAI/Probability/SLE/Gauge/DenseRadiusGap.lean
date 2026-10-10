import OAI.Probability.SLE.Loewner.ActualRadiusStops

namespace OAI

/-! A live current radius level is strictly before every deeper radius
level, including the event that the deeper level is never attained. -/

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.before_deeper_radius_level
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (u q : ℝ) (hu : 0 ≤ u) (hq : 0 < q) (T : ℝ≥0)
    (hz : z ∈ survivingDomain γ T)
    (hR : fullRadius G T z = (2 * z.im) * Real.exp (-u)) :
    (T : ℝ≥0∞) < radiusLevelTime γ G z (u + q) := by
  have hmono := radiusLevelTime_mono hU hw z hu (show u ≤ u + q by linarith)
  rw [radiusLevelTime_eq_of_live_level hU hw z u T hz hR] at hmono
  refine lt_of_le_of_ne hmono ?_
  intro he
  have hfinite : radiusLevelTime γ G z (u + q) < ∞ := by rw [← he]; exact ENNReal.coe_lt_top
  obtain ⟨t, ht, hRt⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z (u + q) hfinite
  have hte := radiusLevelTime_eq_of_live_level hU hw z (u + q) t ht hRt
  have hTt : T = t := by exact_mod_cast (he.trans hte)
  rw [← hTt, hR] at hRt
  have hy : 2 * z.im ≠ 0 := (mul_pos (by norm_num) hz.1.1).ne'
  have hexp := (mul_left_cancel₀ hy hRt)
  have hneg := Real.exp_injective hexp
  linarith

end SLEExactGauge

end

end OAI
