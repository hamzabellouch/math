import OAI.Analysis.MetricEntropy.Parameters
import OAI.Analysis.MetricEntropy.DimensionRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

universe uα

/-!
# From finite compression counts to entropy bounds

The counting premise is the literal finite encoding bound. Its logarithmic
conversion and the exact symmetric-form dimension ratio give the scalar
entropy comparison used after the matrix-to-body construction.
-/

noncomputable section

namespace MetricEntropyDuality

/-- Taking logarithms of the literal finite encoding count. -/
theorem log_count_le_encodingCost {h u q Q : ℕ} {θ : ℝ}
    (hu : 0 < u) (hq : 0 < q) (hθ : 0 < θ) (hQ : 0 < Q)
    (hcount : (Q : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * pivotSlots θ) *
      (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
        (h * pivotSlots θ * 2 ^ u)) :
    Real.log (Q : ℝ) ≤ (h : ℝ) * (pivotSlots θ : ℝ) * Real.log (q : ℝ) +
      encodingCost h θ u := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hbase : 0 < 1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ := by positivity
  calc
    Real.log (Q : ℝ) ≤ Real.log ((u : ℝ) * (q : ℝ) ^ (h * pivotSlots θ) *
        (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
          (h * pivotSlots θ * 2 ^ u)) := Real.log_le_log hQ0 hcount
    _ = (h : ℝ) * (pivotSlots θ : ℝ) * Real.log (q : ℝ) +
        encodingCost h θ u := by
      rw [Real.log_mul (by positivity) (pow_ne_zero _ hbase.ne'),
        Real.log_mul hu0.ne' (pow_ne_zero _ hq0.ne'), Real.log_pow, Real.log_pow]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      unfold encodingCost
      ring

/-- Finite-list version retaining the actual nonempty approximating family. -/
theorem log_card_le_encodingCost {α : Type uα} {A : Finset α} {h u q : ℕ} {θ : ℝ}
    (hu : 0 < u) (hq : 0 < q) (hθ : 0 < θ) (hA : A.Nonempty)
    (hcount : (A.card : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * pivotSlots θ) *
      (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
        (h * pivotSlots θ * 2 ^ u)) :
    Real.log (A.card : ℝ) ≤ (h : ℝ) * (pivotSlots θ : ℝ) * Real.log (q : ℝ) +
      encodingCost h θ u :=
  log_count_le_encodingCost hu hq hθ (Finset.card_pos.mpr hA) hcount

/-- The algebraic ratio calculation before substituting symmetric dimensions. -/
theorem log_square_ratio_le_of_log_bound {Q p D E h s C : ℝ}
    (hp : 1 < p) (hD : 0 < D)
    (hQ : Real.log Q ≤ h * s * E * Real.log p + C) :
    Real.log (Q ^ 2) / (D * Real.log p) ≤
      2 * h * s * (E / D) + 2 * C / (D * Real.log p) := by
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hden : 0 < D * Real.log p := mul_pos hD hlogp
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    2 * Real.log Q / (D * Real.log p) ≤
        (2 * (h * s * E * Real.log p + C)) / (D * Real.log p) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    _ = 2 * h * s * (E / D) + 2 * C / (D * Real.log p) := by
      field_simp [hD.ne', hlogp.ne']

/-- The exact binomial ratio converts label entropy into the rank term. -/
theorem form_entropy_ratio_le {r h s p Q : ℕ} {C : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p)
    (hQ : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      Real.log ((p : ℝ) ^ formDimension r (h - 1)) + C) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) ≤
      2 * (h : ℝ) ^ 2 * (s : ℝ) / ((r : ℝ) + h - 1) +
        2 * C / ((formDimension r h : ℝ) * Real.log (p : ℝ)) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hD : (0 : ℝ) < formDimension r h := by exact_mod_cast formDimension_pos hr
  have hQ' : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      (formDimension r (h - 1) : ℝ) * Real.log (p : ℝ) + C := by
    rw [Real.log_pow] at hQ
    convert hQ using 1; ring
  have hbound := log_square_ratio_le_of_log_bound hp' hD hQ'
  rw [formDimension_prev_div hr hh] at hbound
  have hlogm : Real.log ((p : ℝ) ^ formDimension r h) =
      (formDimension r h : ℝ) * Real.log (p : ℝ) := Real.log_pow _ _
  rw [hlogm]
  convert hbound using 1; ring

/-- Specialization using the actual finite positive-list count and the label
bound `q = p ^ D_(h-1)`. -/
theorem form_entropy_ratio_le_of_count {r h p u Q : ℕ} {θ : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p) (hu : 0 < u)
    (hθ : 0 < θ) (hQ : 0 < Q)
    (hcount : (Q : ℝ) ≤ (u : ℝ) *
      ((p ^ formDimension r (h - 1) : ℕ) : ℝ) ^ (h * pivotSlots θ) *
        (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
          (h * pivotSlots θ * 2 ^ u)) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) ≤
      2 * (h : ℝ) ^ 2 * (pivotSlots θ : ℝ) / ((r : ℝ) + h - 1) +
        2 * encodingCost h θ u / ((formDimension r h : ℝ) * Real.log (p : ℝ)) := by
  apply form_entropy_ratio_le hr hh hp
  have hq : 0 < p ^ formDimension r (h - 1) :=
    pow_pos (by omega : 0 < p) _
  simpa only [Nat.cast_pow] using log_count_le_encodingCost hu hq hθ hQ hcount

end MetricEntropyDuality

end

end OAI
