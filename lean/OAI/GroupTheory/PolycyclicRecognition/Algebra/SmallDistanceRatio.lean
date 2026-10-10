import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartSmallProducts

namespace OAI

/-! # A uniform small-distance threshold for Cartan word coordinates -/

namespace PolycyclicRecognition

/-- The polynomial coordinate bound becomes uniformly small when the
distance is a sufficiently small fraction of a sufficiently large scale. -/
theorem exists_small_distance_ratio (B R : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η S : ℝ, 0 < η ∧ 1 ≤ S ∧ ∀ s : ℝ, S ≤ s → ∀ a : ℝ, 0 ≤ a → a ≤ η * s →
      B * ((a + 1) * R / s) * (1 + (a + 1) * R / s) ^ d ≤ ε := by
  let P : ℝ → ℝ := fun t => B * (t * R) * (1 + t * R) ^ d
  have hP : Continuous P := by dsimp [P]; fun_prop
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp hP.continuousAt ε hε
  let η := δ / 4
  let S := max 1 (4 / δ)
  refine ⟨η, S, by dsimp [η]; positivity, le_max_left _ _, ?_⟩
  intro s hs a ha has
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := by linarith
  have hl : 4 / δ ≤ s := (le_max_right _ _).trans hs
  have hprod : 4 ≤ s * δ := (div_le_iff₀ hδ).mp hl
  have hx0 : 0 ≤ (a + 1) / s := div_nonneg (by linarith) hs0.le
  have hx : (a + 1) / s < δ := by
    apply (div_lt_iff₀ hs0).mpr
    dsimp [η] at has
    nlinarith
  have hh := hsmall (show dist ((a + 1) / s) 0 < δ by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hx0] using hx)
  have he : P 0 = 0 := by simp [P]
  rw [he, Real.dist_eq, sub_zero] at hh
  have hp := (le_abs_self (P ((a + 1) / s))).trans hh.le
  convert hp using 1
  dsimp [P]
  ring

end PolycyclicRecognition

end OAI
