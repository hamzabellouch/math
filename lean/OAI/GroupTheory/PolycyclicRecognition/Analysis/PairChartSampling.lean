import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairErgodic

namespace OAI

/-! # Exact normalized-pair identities for chart sampling

The action in this development is a left action obtained by inverting the
manuscript's right-translation parameter. The identities below keep that
inversion explicit.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- Normalization at the actual chart point, including the deterministic
suffix between the two sampled factors. -/
def chartOccupationPoint (p : NormalizedPair G Λ) (x a k d : G) :
    NormalizedPair G Λ := normalizedTranslate (x * a * k * d) p

omit [ProperSpace G] in
/-- A right move in the second factor changes only that factor. -/
theorem chartOccupationPoint_right_factor (p : NormalizedPair G Λ)
    (x a k d v : G) :
    v⁻¹ • chartOccupationPoint p x a k d =
      chartOccupationPoint p x a k (d * v) := by
  change normalizedTranslate (v⁻¹)⁻¹ (normalizedTranslate (x * a * k * d) p) = _
  rw [inv_inv, normalizedTranslate_mul]
  simp only [chartOccupationPoint, mul_assoc]

omit [ProperSpace G] in
/-- A right move in the normal factor changes the first sampled factor by
the precise conjugate estimated by interior slack. No factorization
uniqueness is needed. -/
theorem chartOccupationPoint_normal_factor (p : NormalizedPair G Λ)
    (x a k d u : G) :
    u⁻¹ • chartOccupationPoint p x a k d =
      chartOccupationPoint p x (a * (k * (d * u * d⁻¹) * k⁻¹)) k d := by
  change normalizedTranslate (u⁻¹)⁻¹ (normalizedTranslate (x * a * k * d) p) = _
  rw [inv_inv, normalizedTranslate_mul]
  simp only [chartOccupationPoint, mul_assoc, inv_mul_cancel, mul_one]

/-- Sampling is continuous in all four group coordinates. -/
theorem continuous_chartOccupationPoint (p : NormalizedPair G Λ) :
    Continuous (fun z : (G × G) × (G × G) =>
      chartOccupationPoint p z.1.1 z.1.2 z.2.1 z.2.2) := by
  have he (x a k d : G) : chartOccupationPoint p x a k d =
      (x * a * k * d)⁻¹ • p := by
    change normalizedTranslate _ p = normalizedTranslate ((x * a * k * d)⁻¹)⁻¹ p
    rw [inv_inv]
  simp_rw [he]
  fun_prop

end PolycyclicRecognition

end

end OAI
