import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseNegativeQuotient

namespace OAI

/-! # Sublinear height errors after changing the basepoint -/

noncomputable section
namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The same linear coefficient works after centering the coarse map at
any fixed source point. Only the additive sublinear-error constant changes. -/
theorem centered_height_sublinear
    (π : G →* Multiplicative W) (A : W →L[ℝ] W) (f : G → G)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖(π (f g)).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B)
    (x : G) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖(π ((f x)⁻¹ * f (x * g))).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := hsub ε hε
  let ex := (π (f x)).toAdd - A ((π x).toAdd)
  refine ⟨B + ε * dist 1 x + ‖ex‖, by positivity, ?_⟩
  intro g
  have he : (π ((f x)⁻¹ * f (x * g))).toAdd - A ((π g).toAdd) =
      ((π (f (x * g))).toAdd - A ((π (x * g)).toAdd)) - ex := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, map_add, ex]
    abel
  have hd : dist (1 : G) (x * g) ≤ dist 1 x + dist 1 g := by
    have hh := dist_triangle (1 : G) x (x * g)
    have he' : dist x (x * g) = dist 1 g := by
      simpa only [mul_one] using dist_mul_left x (1 : G) g
    rwa [he'] at hh
  rw [he]
  calc
    _ ≤ ‖(π (f (x * g))).toAdd - A ((π (x * g)).toAdd)‖ + ‖ex‖ := norm_sub_le _ _
    _ ≤ ε * dist 1 (x * g) + B + ‖ex‖ := add_le_add (hb _) le_rfl
    _ ≤ ε * (dist 1 x + dist 1 g) + B + ‖ex‖ := by gcongr
    _ = _ := by ring

/-- Centering also preserves the coarse Lipschitz constants exactly. -/
theorem centered_coarse_lipschitz (f : G → G) {L C : ℝ}
    (hf : ∀ a b, dist (f a) (f b) ≤ L * dist a b + C) (x a b : G) :
    dist ((f x)⁻¹ * f (x * a)) ((f x)⁻¹ * f (x * b)) ≤ L * dist a b + C := by
  rw [dist_mul_left]
  simpa only [dist_mul_left] using hf (x * a) (x * b)

omit [IsIsometricSMul G G] in
/-- Uniform centered height control supplies the absolute sublinear
estimate used in representative independence. -/
theorem absolute_height_sublinear_of_centered_uniform
    (π : G →* Multiplicative W) (A : W →L[ℝ] W) (f : G → G)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x g,
      ‖(π ((f x)⁻¹ * f (x * g))).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖(π (f g)).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := hsub ε hε
  refine ⟨B + ‖(π (f 1)).toAdd‖, by positivity, ?_⟩
  intro g
  have hh := hb 1 g
  simp only [one_mul, map_mul, map_inv, toAdd_mul, toAdd_inv] at hh
  calc
    _ = ‖(-(π (f 1)).toAdd + (π (f g)).toAdd - A ((π g).toAdd)) + (π (f 1)).toAdd‖ := by
      congr 1
      abel
    _ ≤ ‖-(π (f 1)).toAdd + (π (f g)).toAdd - A ((π g).toAdd)‖ + ‖(π (f 1)).toAdd‖ := norm_add_le _ _
    _ ≤ (ε * dist 1 g + B) + ‖(π (f 1)).toAdd‖ := add_le_add hh le_rfl
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
