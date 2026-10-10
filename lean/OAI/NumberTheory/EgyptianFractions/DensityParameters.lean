import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Exponential ranges in the elementary passage from density to all numerators.
The constants are exactly `D_X = D_M + 2` and `D_C = 4 D_X`. -/
theorem dense_preparation_ranges (DM S : ℝ) (hDM : 1 < DM) (hS : 1 ≤ S) :
    1 < Real.exp (4 * (DM + 2) * S) ∧
    Real.exp S < Real.exp (4 * (DM + 2) * S) ∧
    4 < Real.exp ((DM + 2) * S) ∧
    (Real.exp (4 * (DM + 2) * S)) ^ 2 =
      Real.exp (2 * (4 * (DM + 2)) * S) ∧
    (∀ A M : ℝ, 0 ≤ A → A ≤ Real.exp S →
      0 ≤ M → M ≤ Real.exp (DM * S) →
      A * M ≤ Real.exp ((DM + 2) * S)) := by
  have hS0 : 0 < S := by linarith
  have hDM0 : 0 < DM := by linarith
  have hDX : 3 < (DM + 2) * S := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Real.one_lt_exp_iff.mpr
    positivity
  · apply Real.exp_lt_exp.mpr
    nlinarith
  · have := Real.add_one_le_exp ((DM + 2) * S)
    linarith
  · rw [sq, ← Real.exp_add]
    congr 1
    ring
  · intro A M hA hAb hM hMM
    calc
      A * M ≤ Real.exp S * Real.exp (DM * S) :=
        mul_le_mul hAb hMM hM (Real.exp_pos S).le
      _ = Real.exp (S + DM * S) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((DM + 2) * S) := Real.exp_le_exp.mpr (by nlinarith)

/-- A simultaneous eventual cutoff for all elementary density-parameter
requirements and a supplied lower threshold on `log b`. -/
theorem eventually_dense_preparation_ranges (DM S0 : ℝ) (hDM : 1 < DM) :
    ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      2 ≤ b ∧ S0 ≤ Real.log (b : ℝ) ∧ 1 ≤ Real.log (b : ℝ) ∧
      (b : ℝ) < Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) ∧
      4 < Real.exp ((DM + 2) * Real.log (b : ℝ)) := by
  have ht : Filter.Tendsto (fun b : ℕ => Real.log (b : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := (Filter.eventually_ge_atTop (2 : ℕ)).and
    ((ht.eventually_ge_atTop S0).and (ht.eventually_ge_atTop 1))
  obtain ⟨b0, hb0⟩ := Filter.eventually_atTop.mp he
  refine ⟨b0, fun b hb => ?_⟩
  obtain ⟨hb2, hS0, hS1⟩ := hb0 b hb
  have hr := dense_preparation_ranges DM (Real.log (b : ℝ)) hDM hS1
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  exact ⟨hb2, hS0, hS1, by simpa [Real.exp_log hbpos] using hr.2.1, hr.2.2.1⟩

end Problem337

end

end OAI
