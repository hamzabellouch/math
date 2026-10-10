import OAI.NumberTheory.Ostmann.Construction.TypicalEndpoints

namespace OAI

/-! # Harmonic test errors from the full collision budget -/

namespace Ostmann

open scoped BigOperators Classical

theorem uniform_fiber_test_error (B S : Finset ℕ) (r : ℕ → ℕ) (f : ℕ → ℝ)
    (hr : ∀ a ∈ B, r a ∈ S) :
    residueTestError S (fiberMass B (fun _ => 1 / (B.card : ℝ)) r) f =
      residueTestMean B (fun a => f (r a)) - residueTestMean S f := by
  rw [residueTestError, sum_fiberMass_mul B S _ r f hr]
  simp only [residueTestMean, one_div, ← Finset.mul_sum]
  ring

/-- Passing from the `log(p)` collision budget to harmonic mass only loses
the reciprocal of the smallest `log(p)` in the tested set. -/
theorem harmonic_collision_test_errors (P R : Finset ℕ) (hPR : P ⊆ R)
    (S T : ℕ → Finset ℕ) (μ ν f : ℕ → ℕ → ℝ) (B E : ℝ) (hB : 0 < B)
    (hprime : ∀ p ∈ R, p.Prime)
    (hS : ∀ p ∈ R, (S p).Nonempty) (hT : ∀ p ∈ R, (T p).Nonempty)
    (hcard : ∀ p ∈ R, (S p).card + (T p).card ≤ p)
    (hf : ∀ p ∈ P, ∀ r ∈ S p, |f p r| ≤ 1)
    (hlog : ∀ p ∈ P, B ≤ Real.log (p : ℝ))
    (hbudget : (∑ p ∈ R, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ P, (p : ℝ)⁻¹ * residueTestError (S p) (μ p) (f p) ^ 2) ≤ E / B := by
  apply (le_div_iff₀ hB).mpr
  rw [mul_comm, Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpR := hPR hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hpR).pos
      have hh := collisionDefect_controls_tests p (S p) (T p) (μ p) (ν p) (f p)
        (fun _ => 0) (hS p hpR) (hT p hpR) (hcard p hpR) (hf p hp)
        (by intros; norm_num)
      have hz : residueTestError (T p) (ν p) (fun _ => 0) = 0 := by
        simp [residueTestError, residueTestMean]
      rw [hz, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
      have herr : (p : ℝ)⁻¹ * residueTestError (S p) (μ p) (f p) ^ 2 ≤
          collisionDefect p (S p) (T p) (μ p) (ν p) := by
        apply (le_of_mul_le_mul_left _ hp0)
        calc
          _ = residueTestError (S p) (μ p) (f p) ^ 2 := by field_simp
          _ ≤ _ := hh
      calc
        _ ≤ Real.log (p : ℝ) * ((p : ℝ)⁻¹ * residueTestError (S p) (μ p) (f p) ^ 2) :=
          mul_le_mul_of_nonneg_right (hlog p hp) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left herr (hB.le.trans (hlog p hp))
    _ ≤ ∑ p ∈ R, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hPR
      intro p hp _
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
        (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp))
    _ ≤ E := hbudget

end Ostmann

end OAI
