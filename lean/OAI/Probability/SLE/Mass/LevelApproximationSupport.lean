import OAI.Probability.SLE.Mass.LevelApproximants

namespace OAI

/-! Finite-level mass is carried near the actual past trace. On an
interior compact, the neighborhood shrinks as the level tends to infinity. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma levelApproximationDensity_eq_zero_of_avoidance
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hU : Continuous (fun s => Real.sqrt κ*B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ*B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2*z.im)*Real.exp (-u) < r) (t : ℝ≥0)
    (havoid : ∀ s ∈ Icc 0 t, r ≤ dist (γ ω s) z) :
    levelApproximationDensity κ B γ G u t ω z = 0 := by
  by_contra hn
  have hτ : radiusLevelTime (γ ω) (G ω) z u ≤ (t : ℝ≥0∞) := by
    by_contra h
    exact hn (by simp only [levelApproximationDensity,ite_eq_right h])
  obtain ⟨a,ha,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top (γ ω) (G ω) z u
    (hτ.trans_lt ENNReal.coe_lt_top)
  have hat : a ≤ t := by
    rw [radiusLevelTime_eq_of_live_level hU hw z u a ha hR] at hτ
    exact ENNReal.coe_le_coe.mp hτ
  have hbound := hw.radius_ge_of_no_trace_approach hU a z ha hr hy
    (fun s hs => havoid s ⟨hs.1,hs.2.trans hat⟩)
  exact (not_lt_of_ge hbound) (hR.trans_lt hlevel)

end SLEExactGauge.Multipoint

end

end OAI
