import OAI.Geometry.RuledCovering.Isometries

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Scaled-plane approximation under every Euclidean isometry. -/
theorem physicalHyperbolic : PhysicalHyperbolicStatement := by
  intro h L D v hh hL hD hv hH e he F
  exact (physical_hyperbolic_cover hh hL hD hv hH he).isometry F

lemma norm_plane_sq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma physicalWeight_one (g : Plane) : physicalWeight 1 g = weight g := by
  simp only [physicalWeight, weight, norm_plane_sq, one_pow, one_mul]
  congr 2
  ring

/-- Cyclic permutation from the transverse physical normalization to (p+rv,r). -/
def cycleCoordinates : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (z 2) (z 0)
  invFun z := vec3 (z 2) (z 0) (z 1)
  left_inv z := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' z w := by ext i; fin_cases i <;> rfl
  map_smul' c z := by ext i; fin_cases i <;> rfl
  norm_map' z := by
    change ‖vec3 (z 1) (z 2) (z 0)‖ = ‖z‖
    have hz : z = vec3 (z 0) (z 1) (z 2) := by ext i; fin_cases i <;> rfl
    have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      conv_lhs => rw [hz, norm_vec3_sq]
    have ht := norm_vec3_sq (z 1) (z 2) (z 0)
    nlinarith [norm_nonneg (vec3 (z 1) (z 2) (z 0)), norm_nonneg z]

lemma cycle_physicalRuled (D : Set Plane) (v : Plane → Plane) (L : ℝ) :
    cycleCoordinates '' physicalRuled 1 D v L = ruled D v L := by
  ext z
  constructor
  · rintro ⟨_, ⟨p, hp, r, hr, rfl⟩, rfl⟩
    exact ⟨p, hp, r, hr, by simp [cycleCoordinates]⟩
  · rintro ⟨p, hp, r, hr, rfl⟩
    refine ⟨vec3 r (p 0+r*v p 0) (p 1+r*v p 1),
      ⟨p, hp, r, hr, by simp⟩, ?_⟩
    rfl

/-- General hyperbolic approximation: arbitrary compact labels, including
positive-area frontiers and area-zero sets. -/
theorem hyperbolic : HyperbolicStatement := by
  intro D v L hD hv hL hH e he
  have hc := physicalHyperbolic 1 L D v (by norm_num) hL hD hv hH e he
    cycleCoordinates.toIsometryEquiv
  simpa only [LinearIsometryEquiv.coe_toIsometryEquiv, cycle_physicalRuled,
    physicalWeight_one, one_mul] using hc

end RuledApproximation

end

end OAI
