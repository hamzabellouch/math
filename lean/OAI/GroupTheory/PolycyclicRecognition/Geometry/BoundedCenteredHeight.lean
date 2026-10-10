import OAI.GroupTheory.PolycyclicRecognition.Geometry.CenteredHeightError

namespace OAI

/-! # Uniform height control on families with bounded centers -/

noncomputable section
namespace PolycyclicRecognition

/-- On a family with bounded image centers, a uniform centered height
estimate gives an uncentered estimate with one common additive constant. -/
theorem bounded_family_height_of_centered_uniform
    {G W P : Type*} [Group G] [MetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G →* Multiplicative W) (A : W →L[ℝ] W) (f : G → G)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x g,
      ‖(π ((f x)⁻¹ * f (x * g))).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B)
    (center : P → G) {start : ℝ} (hstart : ∀ p, dist 1 (f (center p)) ≤ start) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(π (f (center p * g))).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := hsub ε hε
  refine ⟨B + K * |start|, by positivity, ?_⟩
  intro p g
  have hcenter : ‖(π (f (center p))).toAdd‖ ≤ K * |start| := by
    have hh := hLip (f (center p)) 1
    simp only [map_one, toAdd_one, sub_zero] at hh
    have hd : dist (f (center p)) 1 ≤ |start| := by
      simpa only [dist_comm] using (hstart p).trans (le_abs_self start)
    exact hh.trans (mul_le_mul_of_nonneg_left hd hK)
  have he : (π (f (center p * g))).toAdd - A ((π g).toAdd) =
      ((π ((f (center p))⁻¹ * f (center p * g))).toAdd - A ((π g).toAdd)) +
        (π (f (center p))).toAdd := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [hb (center p) g])

end PolycyclicRecognition

end

end OAI
