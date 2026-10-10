import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-! The elementary second-derivative test used by the scalar maximum
principle, stated for the actual derivative functions along frame curves. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped Topology

theorem scalar_second_derivative_nonneg_at_local_min
    {f f₁ f₂ : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (hc : ContinuousAt f₂ a) (hmin : IsLocalMin f a) : 0 ≤ f₂ a := by
  by_contra hn
  have hneg : f₂ a < 0 := lt_of_not_ge hn
  have hnear : ∀ᶠ t in 𝓝 a, f₂ t < 0 ∧ f a ≤ f t :=
    (hc.eventually (gt_mem_nhds hneg)).and hmin
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let b := a + ε / 2
  have hab : a < b := by dsimp [b]; linarith
  have hin (t : ℝ) (ht : t ∈ Icc a b) : t ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    dsimp [b] at ht
    linarith [ht.2]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hanti₁ : StrictAntiOn f₁ (Icc a b) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b)
      (continuous_iff_continuousAt.mpr (fun t => (hf₁ t).continuousAt)).continuousOn
    · intro t _
      exact (hf₁ t).hasDerivWithinAt
    · intro t ht
      exact (hball (hin t (interior_subset ht))).1
  have hz : f₁ a = 0 := hmin.hasDerivAt_eq_zero (hf a)
  have hanti : StrictAntiOn f (Icc a b) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b)
      (continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)).continuousOn
    · intro t _
      exact (hf t).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      simpa only [hz] using hanti₁ ha (interior_subset ht) ht'.1
  exact (not_lt_of_ge (hball (hin b hb)).2) (hanti ha hb hab)

end PositiveEinsteinFour.Geometry

end OAI
