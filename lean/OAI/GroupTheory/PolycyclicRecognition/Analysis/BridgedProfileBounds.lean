import OAI.GroupTheory.PolycyclicRecognition.Geometry.SheetEndpointHeight

namespace OAI

/-! # One common error for path lifting and endpoint accumulation -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Normalize the two pivot-bridge errors into the same tolerance used by
the Cartan tuple lifting theorem. The endpoint bound has no logarithmic term. -/
theorem exists_bridged_profile_bounds
    {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hpath : ∀ a b : X, ∃ γ : Path a b, PathMetricBound γ (dist a b) 0)
    {a a' b' b : X} (middle : Path a' b')
    {C r δ ε : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hm : PathMetricBound middle (C * r) (C * (1 + Real.log (2 + r))))
    (ha : dist a a' ≤ δ * r) (hb : dist b' b ≤ δ * r)
    (J : X → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (E : Set W) (hE0 : (0 : W) ∈ E)
    (himage : ∀ t, ∃ w ∈ E, ‖J (middle t) - J a' - r • w‖ ≤
      2 * r * ε + C * (1 + Real.log (2 + r)))
    (hend : ‖J b' - J a'‖ ≤ 2 * r * ε) :
    let η := 2 * ε + 2 * K * δ
    let A := 4 * (C + 1)
    ∃ γ : Path a b,
      PathMetricBound γ (A * r) (A * (1 + Real.log (2 + r))) ∧
      (∀ t, ∃ w ∈ E, ‖J (γ t) - J a - r • w‖ ≤
        2 * r * η + A * (1 + Real.log (2 + r))) ∧
      ‖J b - J a‖ ≤ η * r := by
  dsimp only
  have hr0 : 0 ≤ r := by linarith
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (show 1 ≤ 2 + r by linarith)
    linarith
  have hκ := mul_nonneg hC hlog
  have hB : 0 ≤ 2 * r * ε + C * (1 + Real.log (2 + r)) := by positivity
  obtain ⟨path, hmetric, hheight⟩ := exists_bridged_profile_path hpath middle hκ
    (mul_nonneg hδ hr0) hB hm ha hb J hJ E hE0 himage
  have hsmall := endpoint_height_of_short_bridges J hJ ha hb hend
  refine ⟨path, hmetric.mono ?_ ?_, ?_, ?_⟩
  · rw [max_eq_left (mul_nonneg hC hr0)]
    nlinarith [mul_le_mul_of_nonneg_right hδ1 hr0]
  · nlinarith
  · intro t
    obtain ⟨w, hw, he⟩ := hheight t
    refine ⟨w, hw, he.trans ?_⟩
    have hη : 0 ≤ 2 * ε + 2 * K * δ := by positivity
    have heq : 2 * r * ε + C * (1 + Real.log (2 + r)) + 2 * K * (δ * r) =
        r * (2 * ε + 2 * K * δ) + C * (1 + Real.log (2 + r)) := by ring
    rw [heq]
    nlinarith [mul_nonneg hr0 hη]
  · convert hsmall using 1; ring

end PolycyclicRecognition

end

end OAI
