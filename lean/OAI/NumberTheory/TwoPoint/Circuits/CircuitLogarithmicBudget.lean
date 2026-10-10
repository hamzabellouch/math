import OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialGrowth

namespace OAI

/-! Convert a dyadic accuracy index to the natural logarithm used in the
published fixed-depth bounded-independence input. -/

namespace TwoPointCorrelations

lemma dyadic_index_of_ratio (m : ℕ) (hm : 1 ≤ m) (ε : ℝ)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ j : ℕ, m ≤ 2 ^ j ∧ (1 / 2 : ℝ) ^ j ≤ ε ∧
      (j : ℝ) + 1 ≤ 6 * Real.log ((m : ℝ) / ε) := by
  let L := Real.log ((m : ℝ) / ε)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hratio : (2 : ℝ) ≤ (m : ℝ) / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hL : 1 / 2 ≤ L := hlogtwo.trans (Real.log_le_log (by norm_num) hratio)
  let j := ⌈2 * L⌉₊
  have hjlo : 2 * L ≤ (j : ℝ) := Nat.le_ceil _
  have hjhi : (j : ℝ) < 2 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlogbound : L ≤ (j : ℝ) * Real.log 2 := by
    nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hx : (m : ℝ) / ε ≤ (2 : ℝ) ^ j := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simpa only [Real.log_pow] using hlogbound
  have hmul : (m : ℝ) ≤ (2 : ℝ) ^ j * ε := (div_le_iff₀ hε).mp hx
  have hmle : (m : ℝ) ≤ (2 : ℝ) ^ j := by nlinarith [show (0 : ℝ) < 2 ^ j by positivity]
  have heps : (1 / 2 : ℝ) ^ j ≤ ε := by
    have hh : (1 : ℝ) / (2 : ℝ) ^ j ≤ ε :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    simpa only [div_pow, one_pow] using hh
  exact ⟨j, by exact_mod_cast hmle, heps, by linarith⟩

theorem bravermanDegree_logarithmic_budget :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((m : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∃ j : ℕ, m ≤ 2 ^ j ∧ (1 / 2 : ℝ) ^ j ≤ ε ∧ bravermanDegree j ≤ t := by
  obtain ⟨K, C, hK, hC, hbound⟩ := bravermanDegree_polynomial_positive
  refine ⟨K * 6 ^ C, C, by positivity, hC, ?_⟩
  intro m hm ε hε hεhalf t ht
  obtain ⟨j, hmj, hjε, hjlog⟩ := dyadic_index_of_ratio m hm ε hε hεhalf
  refine ⟨j, hmj, hjε, ?_⟩
  have hj : (bravermanDegree j : ℝ) ≤ (K : ℝ) * ((j : ℝ) + 1) ^ C := by
    exact_mod_cast hbound j
  have hdeg : (bravermanDegree j : ℝ) ≤ (t : ℝ) := by
    calc
      _ ≤ _ := hj
      _ ≤ (K : ℝ) * (6 * Real.log ((m : ℝ) / ε)) ^ C := by gcongr
      _ = ((K * 6 ^ C : ℕ) : ℝ) * (Real.log ((m : ℝ) / ε)) ^ C := by
        push_cast
        rw [mul_pow]
        ring
      _ ≤ _ := ht
  exact_mod_cast hdeg

end TwoPointCorrelations

end OAI
