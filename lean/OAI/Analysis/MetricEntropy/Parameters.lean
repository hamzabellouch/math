import OAI.Analysis.MetricEntropy.FormDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Parameters fixed before the prime is chosen

These are the literal accuracy, pivot-slot, direction-count and encoding-cost
parameters of the construction. The radius and rank are genuinely available
for every proposed comparison constant. Their existence does not depend on
the eventual field size.
-/

noncomputable section

namespace MetricEntropyDuality

def accuracy (a : ℝ) : ℝ := 1 / (1000 * a)

def pivotSlots (θ : ℝ) : ℕ := Nat.ceil (1 / θ)

/-- A fixed positive radius satisfying the logarithmic compression condition. -/
def compressionRadius (a : ℝ) : ℕ :=
  Nat.ceil (Real.exp (Real.log 3 / accuracy a)) + 1

def directionCount (r h : ℕ) (θ : ℝ) : ℕ :=
  Nat.ceil ((h : ℝ) * (2 * (formDimension r h : ℝ)) / θ)

def encodingCost (h : ℕ) (θ : ℝ) (u : ℕ) : ℝ :=
  Real.log (u : ℝ) + (h : ℝ) * (pivotSlots θ : ℝ) * (2 : ℝ) ^ u *
    Real.log (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ)

theorem accuracy_pos {a : ℝ} (ha : 1 ≤ a) : 0 < accuracy a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  unfold accuracy
  positivity

theorem accuracy_lt_one {a : ℝ} (ha : 1 ≤ a) : accuracy a < 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  rw [accuracy, div_lt_one (by positivity : (0 : ℝ) < 1000 * a)]
  linarith

theorem accuracy_cover_scale {a : ℝ} (ha : 1 ≤ a) :
    38 * accuracy a < a⁻¹ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have heq : 38 * accuracy a = ((38 : ℝ) / 1000) / a := by
    unfold accuracy
    field_simp [ha0.ne']
  rw [heq, ← one_div]
  exact (div_lt_div_iff_of_pos_right ha0).mpr (by norm_num)

theorem one_div_le_pivotSlots (θ : ℝ) : 1 / θ ≤ (pivotSlots θ : ℝ) :=
  Nat.le_ceil _

theorem pivotSlots_pos {θ : ℝ} (hθ : 0 < θ) : 0 < pivotSlots θ := by
  apply Nat.ceil_pos.mpr
  exact one_div_pos.mpr hθ

theorem one_le_mul_pivotSlots {θ : ℝ} (hθ : 0 < θ) :
    1 ≤ θ * (pivotSlots θ : ℝ) := by
  have hs := (div_le_iff₀ hθ).mp (one_div_le_pivotSlots θ)
  simpa only [mul_comm] using hs

theorem compressionRadius_pos (a : ℝ) : 0 < compressionRadius a :=
  Nat.succ_pos _

theorem compressionRadius_log_pos (a : ℝ) :
    0 < Real.log ((compressionRadius a : ℝ) + 1) := by
  apply Real.log_pos
  have hh : (0 : ℝ) < compressionRadius a := Nat.cast_pos.mpr (compressionRadius_pos a)
  linarith

theorem compressionRadius_log_le {a : ℝ} (ha : 1 ≤ a) :
    Real.log 3 / Real.log ((compressionRadius a : ℝ) + 1) ≤ accuracy a := by
  have hθ := accuracy_pos ha
  have hceil := Nat.le_ceil (Real.exp (Real.log 3 / accuracy a))
  have hbound : Real.exp (Real.log 3 / accuracy a) < (compressionRadius a : ℝ) + 1 := by
    simp only [compressionRadius, Nat.cast_add, Nat.cast_one]
    linarith
  have hlog := Real.log_lt_log (Real.exp_pos (Real.log 3 / accuracy a)) hbound
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ (compressionRadius_log_pos a)).mpr
  have hmul := (div_lt_iff₀ hθ).mp hlog
  nlinarith

/-- The rank can be chosen after the compression parameters and before the prime. -/
theorem exists_rank (b θ : ℝ) {h : ℕ} (hh : 0 < h) :
    ∃ r : ℕ, 0 < r ∧
      8 * b * (h : ℝ) ^ 2 * (pivotSlots θ : ℝ) < (r : ℝ) + h - 1 := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 (8 * b * (h : ℝ) ^ 2 * (pivotSlots θ : ℝ)))
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hrbound := lt_of_le_of_lt (le_max_right _ _) hr
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.succ_le_of_lt hh)
  refine ⟨r, Nat.cast_pos.mp hr0, ?_⟩
  linarith

theorem directionCount_pos {r h : ℕ} {θ : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hθ : 0 < θ) :
    0 < directionCount r h θ := by
  apply Nat.ceil_pos.mpr
  have hD : (0 : ℝ) < formDimension r h := Nat.cast_pos.mpr (formDimension_pos hr)
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  positivity

/-- The natural ceiling has exactly the direction needed by the deletion argument. -/
theorem directionCount_budget {r h : ℕ} {θ : ℝ} (hθ : 0 < θ) :
    (h : ℝ) * (2 * (formDimension r h : ℝ)) ≤ θ * (directionCount r h θ : ℝ) := by
  have hu : (h : ℝ) * (2 * (formDimension r h : ℝ)) / θ ≤
      (directionCount r h θ : ℝ) := Nat.le_ceil _
  have hmul := (div_le_iff₀ hθ).mp hu
  simpa only [mul_comm] using hmul

theorem encodingCost_pos {h u : ℕ} {θ : ℝ}
    (hh : 0 < h) (hθ : 0 < θ) (hu : 0 < u) : 0 < encodingCost h θ u := by
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hsR : (0 : ℝ) < pivotSlots θ := Nat.cast_pos.mpr (pivotSlots_pos hθ)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ u := by positivity
  have hquot : 0 < (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ :=
    div_pos (mul_pos hsR hpow) hθ
  have hlog : 0 < Real.log (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) :=
    Real.log_pos (by linarith)
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (Nat.succ_le_of_lt hu)
  exact add_pos_of_nonneg_of_pos (Real.log_nonneg hu1)
    (mul_pos (mul_pos (mul_pos hhR hsR) hpow) hlog)

/-- Simultaneous scalar choices, with all dependent quantities already fixed. -/
theorem exists_parameters {a : ℝ} (ha : 1 ≤ a) (b : ℝ) :
    ∃ h r : ℕ, h = compressionRadius a ∧ 0 < h ∧ 0 < r ∧
      Real.log 3 / Real.log ((h : ℝ) + 1) ≤ accuracy a ∧
      8 * b * (h : ℝ) ^ 2 * (pivotSlots (accuracy a) : ℝ) < (r : ℝ) + h - 1 ∧
      0 < formDimension r h ∧
      0 < directionCount r h (accuracy a) ∧
      (h : ℝ) * (2 * (formDimension r h : ℝ)) ≤
        accuracy a * (directionCount r h (accuracy a) : ℝ) ∧
      0 < encodingCost h (accuracy a) (directionCount r h (accuracy a)) := by
  let h := compressionRadius a
  have hh : 0 < h := compressionRadius_pos a
  obtain ⟨r, hr, hrbound⟩ := exists_rank b (accuracy a) hh
  have hθ := accuracy_pos ha
  have hu := directionCount_pos hr hh hθ
  exact ⟨h, r, rfl, hh, hr, compressionRadius_log_le ha, hrbound,
    formDimension_pos hr, hu, directionCount_budget hθ, encodingCost_pos hh hθ hu⟩

end MetricEntropyDuality

end

end OAI
