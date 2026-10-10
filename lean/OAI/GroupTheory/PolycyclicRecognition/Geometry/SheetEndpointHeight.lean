import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileChainHeightBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConjugatedSheetPaths

namespace OAI

/-! # Small endpoint heights at the common facet pivot -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- At one chart point only the common limiting value matters. In
particular, the offset and linear part of the affine profile cancel. -/
theorem common_profile_endpoint_height
    {G W Z : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) (x k l d : G) (r : ℝ) (φ : Z → G) (z₀ : Z) (c : W)
    (hd : φ z₀ = d) {ε : ℝ}
    (hk : ‖rescaledMapProfile J x k r φ z₀ - c‖ ≤ ε)
    (hl : ‖rescaledMapProfile J x l r φ z₀ - c‖ ≤ ε) :
    ‖J (x * l * d) - J (x * k * d)‖ ≤ 2 * Real.exp r * ε := by
  have he := relative_height_of_common_affine_profiles J x l k r φ
    (fun _ : Z => (0 : W)) (0 : W →ₗ[ℝ] W) c z₀ z₀ (by simpa using hl) (by simpa using hk)
  simpa only [hd, sub_self, map_zero, smul_zero, sub_zero, mul_add,
    two_mul, add_mul] using he

/-- A short bridge at each endpoint adds twice its Lipschitz image to the
endpoint height error. This is separate from control of the whole path. -/
theorem endpoint_height_of_short_bridges
    {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W]
    (J : X → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    {a a' b' b : X} {δ B : ℝ}
    (ha : dist a a' ≤ δ) (hb : dist b' b ≤ δ)
    (hmid : ‖J b' - J a'‖ ≤ B) :
    ‖J b - J a‖ ≤ B + 2 * K * δ := by
  have hleft : ‖J a' - J a‖ ≤ K * δ := by
    rw [← dist_eq_norm]
    exact (hJ.dist_le_mul a' a).trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using ha) K.coe_nonneg)
  have hright : ‖J b - J b'‖ ≤ K * δ := by
    rw [← dist_eq_norm]
    exact (hJ.dist_le_mul b b').trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hb) K.coe_nonneg)
  calc
    ‖J b - J a‖ = ‖(J b - J b') + (J b' - J a') + (J a' - J a)‖ := by congr 1; abel
    _ ≤ ‖J b - J b'‖ + ‖J b' - J a'‖ + ‖J a' - J a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ K * δ + B + K * δ := add_le_add (add_le_add hright hmid) hleft
    _ = B + 2 * K * δ := by ring

end PolycyclicRecognition

end

end OAI
