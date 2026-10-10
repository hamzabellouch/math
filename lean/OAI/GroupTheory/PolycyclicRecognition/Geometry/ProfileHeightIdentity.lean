import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairChartSampling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PairHeightCocycle

namespace OAI

/-! # Exact height increments of sampled profiles -/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G W Z : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}

omit [ProperSpace G] [NormedSpace ℝ W] in
/-- Normalization at a chart point subtracts exactly its starting height. -/
theorem pairHeight_chartOccupationPoint (π : G →* Multiplicative W)
    (p : NormalizedPair G Λ) (x a k y d : G) :
    pairHeight π d (chartOccupationPoint p x a k y) =
      (π (p.val.1 (x * a * k * y * d))).toAdd -
        (π (p.val.1 (x * a * k * y))).toAdd := by
  change (π ((p.val.1 (x * a * k * y))⁻¹ *
    p.val.1 ((x * a * k * y) * d))).toAdd = _
  rw [map_mul, map_inv]
  simp only [toAdd_mul, toAdd_inv]
  abel

omit [ProperSpace G] in
/-- The increment along the actual scaled path is the normalized pair
cocycle, with the same total time used in the microstep estimate. -/
theorem rescaledMapProfile_increment_eq_pairHeight
    (π : G →* Multiplicative W) (p : NormalizedPair G Λ)
    (x a k : G) (r T : ℝ) (φ : Z → G) (z w : Z) (d : G)
    (hend : φ w = φ z * d) :
    T⁻¹ • (rescaledMapProfile (fun g => (π (p.val.1 g)).toAdd) x (a * k) r φ w -
      rescaledMapProfile (fun g => (π (p.val.1 g)).toAdd) x (a * k) r φ z) =
      (Real.exp r * T)⁻¹ • pairHeight π d (chartOccupationPoint p x a k (φ z)) := by
  rw [pairHeight_chartOccupationPoint]
  simp only [rescaledMapProfile, hend, mul_assoc, ← smul_sub,
    sub_sub_sub_cancel_right, smul_smul, mul_inv_rev]

end PolycyclicRecognition

end

end OAI
