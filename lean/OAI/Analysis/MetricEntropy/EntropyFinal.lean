import OAI.Analysis.MetricEntropy.EntropyBounds
import OAI.Analysis.MetricEntropy.EntropyComparison

namespace OAI

/-!
# Scalar consequences of the rank and prime choices

These lemmas retain the explicit finite compression bound. They do not assume
the existence of a matrix or a convex body; those constructions insert their
actual cardinalities and covering inequalities into these estimates.
-/

noncomputable section

namespace MetricEntropyDuality

/-- The exact dimension ratio and the two numerical choices give a strict
entropy ratio for the signed approximation list. -/
theorem form_entropy_ratio_lt {r h s p Q : ℕ} {C b : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p) (hb : 1 ≤ b) (hC : 0 ≤ C)
    (hQ : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      Real.log ((p : ℝ) ^ formDimension r (h - 1)) + C)
    (hrank : 8 * b * (h : ℝ) ^ 2 * (s : ℝ) < (r : ℝ) + h - 1)
    (hprime : Real.exp (8 * b * C / (formDimension r h : ℝ)) < (p : ℝ)) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) <
      1 / (2 * b) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hD : (0 : ℝ) < formDimension r h := by exact_mod_cast formDimension_pos hr
  have hscalar := entropy_budget_lt hb hC hD
    (show 0 ≤ (h : ℝ) ^ 2 * (s : ℝ) by positivity)
    (show 8 * b * ((h : ℝ) ^ 2 * (s : ℝ)) < (r : ℝ) + h - 1 by
      convert hrank using 1; ring) hprime hp'
  apply lt_of_le_of_lt (form_entropy_ratio_le hr hh hp hQ)
  simpa only [mul_assoc] using hscalar

/-- The strict entropy bound directly from the literal finite count. -/
theorem form_entropy_ratio_lt_of_count {r h p u Q : ℕ} {θ b : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p) (hu : 0 < u)
    (hθ : 0 < θ) (hQ : 0 < Q) (hb : 1 ≤ b)
    (hcount : (Q : ℝ) ≤ (u : ℝ) *
      ((p ^ formDimension r (h - 1) : ℕ) : ℝ) ^ (h * pivotSlots θ) *
        (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
          (h * pivotSlots θ * 2 ^ u))
    (hrank : 8 * b * (h : ℝ) ^ 2 * (pivotSlots θ : ℝ) < (r : ℝ) + h - 1)
    (hprime : Real.exp (8 * b * encodingCost h θ u / (formDimension r h : ℝ)) <
      (p : ℝ)) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) <
      1 / (2 * b) := by
  apply form_entropy_ratio_lt hr hh hp hb (encodingCost_pos hh hθ hu).le _ hrank hprime
  have hq : 0 < p ^ formDimension r (h - 1) := pow_pos (by omega : 0 < p) _
  simpa only [Nat.cast_pow] using log_count_le_encodingCost hu hq hθ hQ hcount

/-- Choosing the prime after the rank gives the explicit vanishing-ratio bound.
The fixed encoding cost may depend on the rank before the prime is selected. -/
theorem form_entropy_ratio_le_rank {r h s p Q : ℕ} {C : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p) (hC : 0 ≤ C)
    (hQ : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      Real.log ((p : ℝ) ^ formDimension r (h - 1)) + C)
    (hprime : Real.exp ((r : ℝ) * C / (formDimension r h : ℝ)) < (p : ℝ)) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) ≤
      2 * (h : ℝ) ^ 2 * (s : ℝ) / ((r : ℝ) + h - 1) + 2 / (r : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hD : (0 : ℝ) < formDimension r h := by exact_mod_cast formDimension_pos hr
  exact (form_entropy_ratio_le hr hh hp hQ).trans
    (add_le_add (le_refl _) (encoding_ratio_le hr' hC hD hprime hp'))

end MetricEntropyDuality

end

end OAI
