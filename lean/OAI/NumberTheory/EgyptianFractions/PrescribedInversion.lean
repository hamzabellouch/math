import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Slack in a reciprocal bound, including nonpositive slopes. -/
theorem exists_positive_slack {A c : ℝ} (hA : 0 < A) (hc : c < 1 / A) :
    ∃ ε : ℝ, 0 < ε ∧ c * (A + ε) < 1 := by
  have hAc : c * A < 1 := (lt_div_iff₀ hA).mp hc
  by_cases hc0 : c ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    have : c * (A + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 (by linarith)
    linarith
  · have hcpos : 0 < c := lt_of_not_ge hc0
    refine ⟨(1 / c - A) / 2, ?_, ?_⟩
    · have : A < 1 / c := (lt_div_iff₀ hcpos).mpr (by nlinarith)
      linarith
    · have hcancel : c * (1 / c) = 1 := by field_simp
      nlinarith

/-- Abstract inversion of a short marked-expansion bound.

The hypotheses isolate the combinatorial work: finite initial intervals are eventually
covered, marked expansions can be padded from length at least three, and large markers
have asymptotically short expansions. -/
theorem eventual_double_exp_lower_of_short_markers
    (D : ℕ → Set ℕ) (v : ℕ → ℕ) (A : ℝ) (hA : 0 < A)
    (hmissing : ∀ k, 2 ≤ v k ∧ v k ∉ D k)
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ m : ℕ, 2 ≤ m → m < M → m ∈ D k)
    (hpad : ∀ r k : ℕ, 3 ≤ r → r ≤ k → D r ⊆ D k)
    (hshort : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ r : ℕ, 3 ≤ r ∧ m ∈ D r ∧
        (r : ℝ) ≤ (A + ε) * Real.log (Real.log (m : ℝ))) :
    ∀ c : ℝ, c < 1 / A → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ) := by
  intro c hc
  obtain ⟨ε, hε, hcoef⟩ := exists_positive_slack hA hc
  obtain ⟨M, hM, hshortM⟩ := hshort ε hε
  obtain ⟨K, hK⟩ := hsmall M
  refine ⟨K, ?_⟩
  intro k hk
  by_contra hnot
  have hvlt : (v k : ℝ) < Real.exp (Real.exp (c * (k : ℝ))) := lt_of_not_ge hnot
  obtain ⟨hv2, hvmissing⟩ := hmissing k
  have hvM : M ≤ v k := by
    by_contra h
    exact hvmissing (hK k hk (v k) hv2 (lt_of_not_ge h))
  obtain ⟨r, hr3, hmem, hrlen⟩ := hshortM (v k) hvM
  have hv1 : (1 : ℝ) < (v k : ℝ) := by exact_mod_cast (show 1 < v k by omega)
  have hvpos : (0 : ℝ) < (v k : ℝ) := by linarith
  have hlogpos : 0 < Real.log (v k : ℝ) := Real.log_pos hv1
  have hlog : Real.log (v k : ℝ) ≤ Real.exp (c * (k : ℝ)) := by
    simpa only [Real.log_exp] using Real.log_le_log hvpos hvlt.le
  have hloglog : Real.log (Real.log (v k : ℝ)) ≤ c * (k : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log hlogpos hlog
  have hrkR : (r : ℝ) ≤ (k : ℝ) := calc
    (r : ℝ) ≤ (A + ε) * Real.log (Real.log (v k : ℝ)) := hrlen
    _ ≤ (A + ε) * (c * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hloglog (by linarith)
    _ = (c * (A + ε)) * (k : ℝ) := by ring
    _ ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hcoef.le (Nat.cast_nonneg k)
    _ = (k : ℝ) := one_mul _
  have hrk : r ≤ k := by exact_mod_cast hrkR
  exact hvmissing (hpad r k hr3 hrk hmem)

end Problem337

end

end OAI
