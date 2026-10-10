import OAI.Combinatorics.ProgressionColoring.UniformBudget
import OAI.Combinatorics.ProgressionColoring.ScalarEntropy

namespace OAI

noncomputable section

open Filter Topology
open scoped BigOperators

namespace QuantitativeVanDerWaerden.Parameters

/-- The integer anchored-pattern sum on the half-open interval is exactly the
real-power local tail already estimated above. -/
theorem outer_local_sum_eq_localTail (k : ℕ) :
    (∑ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k),
      (((16005 * dimension k * h) ^ (14 * dimension k) : ℕ) : ℝ) *
        Real.exp (-(h : ℝ) / 64)) = localTail 16005 14 k := by
  have hinterval : Finset.Ioc (dimension k ^ 2) (2 * cutoff k) =
      Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k) := by
    ext h
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.lt_iff_add_one_le]
  rw [hinterval]
  unfold localTail
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  norm_num

/-- The actual finite row and anchored-pattern weights obey the required
incident budget.  The row count may be zero. -/
theorem eventually_outer_counted_budget :
    ∀ᶠ k : ℕ in atTop, ∀ L F : ℝ, 1 ≤ L → 1 ≤ F → ∀ T : ℕ,
      Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) →
      F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k →
      (T : ℝ) ≤ (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^
        (2 * dimension k) →
      ((k * T : ℕ) : ℝ) * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) +
        (∑ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k),
          (((16005 * dimension k * h) ^ (14 * dimension k) : ℕ) : ℝ) *
            Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500 := by
  have hbudget := eventually_incident_budget
    (G := (520 : ℝ)) (C := (16005 : ℝ)) (a := (14 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (32 : ℕ), hbudget]
    with k hk hb L F hL hF T hLlog hmesh hcount
  rw [outer_local_sum_eq_localTail]
  by_cases hT : T = 0
  · subst T
    simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, zero_add]
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    have hzero : Real.log (1 : ℝ) ≤
        520 * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
      rw [Real.log_one]
      positivity
    have hone := hb 1 (by norm_num) hzero
    have hrow : 0 ≤ (k : ℝ) * 1 *
        Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) := by positivity
    linarith
  · have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
    have hentropy := log_global_count_le (e := 6) hk hL hF hTpos hLlog hmesh hcount
    have hentropy' : Real.log (T : ℝ) ≤
        520 * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
      norm_num at hentropy
      exact hentropy
    simpa only [Nat.cast_mul] using (hb T hTpos hentropy').le

/-- A single absolute integer threshold works for every admissible finite
direction, mesh and row count. -/
theorem exists_outer_counted_threshold :
    ∃ K : ℕ, 32 ≤ K ∧ ∀ k ≥ K, ∀ L F : ℝ, 1 ≤ L → 1 ≤ F → ∀ T : ℕ,
      Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) →
      F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k →
      (T : ℝ) ≤ (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^
        (2 * dimension k) →
      ((k * T : ℕ) : ℝ) * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) +
        (∑ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k),
          (((16005 * dimension k * h) ^ (14 * dimension k) : ℕ) : ℝ) *
            Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500 := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((eventually_ge_atTop (32 : ℕ)).and eventually_outer_counted_budget)
  exact ⟨K, (hK K le_rfl).1, fun k hk => (hK k hk).2⟩

end QuantitativeVanDerWaerden.Parameters

end

end OAI
