import OAI.GroupTheory.PolycyclicRecognition.Algebra.ShortSheetBridges

namespace OAI

/-! # Returning a conjugated bundle to the common pivot sheet -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G W : Type*} [Group N] [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The same pivot bridge bound applies at both ends of every bundle;
the initial good state and its accumulated prefix cancel by left invariance. -/
theorem exists_common_sheet_word_path
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (ι : N →* G) (x d : G) (n n' k : N)
    (middle : Path (x * ι (n * k) * d) (x * ι (n' * k) * d))
    {L κ δ B r : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hm : PathMetricBound middle L κ) (hk : dist d (ι k * d) ≤ δ)
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (E : Set W) (hE0 : (0 : W) ∈ E)
    (himage : ∀ t, ∃ w ∈ E,
      ‖J (middle t) - J (x * ι (n * k) * d) - r • w‖ ≤ B) :
    ∃ γ : Path (x * ι n * d) (x * ι n' * d),
      PathMetricBound γ (4 * (max L 0 + δ)) (4 * κ) ∧
      ∀ t, ∃ w ∈ E, ‖J (γ t) - J (x * ι n * d) - r • w‖ ≤ B + 2 * K * δ := by
  have hdist (q : N) : dist (x * ι q * d) (x * ι (q * k) * d) =
      dist d (ι k * d) := by
    simpa only [map_mul, mul_assoc] using dist_mul_left (x * ι q) d (ι k * d)
  apply exists_bridged_profile_path
    (exists_short_path_of_minimizing_paths hpath) middle hκ hδ hB hm
    ((hdist n).trans_le hk) (by rw [dist_comm, hdist]; exact hk)
    J hJ E hE0 himage

end PolycyclicRecognition

end

end OAI
