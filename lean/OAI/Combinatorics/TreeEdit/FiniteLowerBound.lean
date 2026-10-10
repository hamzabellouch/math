import OAI.Combinatorics.TreeEdit.FiniteParameters
import OAI.Combinatorics.TreeEdit.CapInversion

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteTree

lemma length_log_bound {k : ℕ} (hk : 20 ≤ k) :
    Real.log (binaryLength k : ℝ) ≤ 100 * (k : ℝ) ^ 2 * Real.log k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hl0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hl20 : Real.log 20 ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  simp only [binaryLength, wordLength, branching, repetitions, Nat.cast_pow, Nat.cast_mul,
    Nat.cast_ofNat, Real.log_pow]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow]
  push_cast
  calc
    _ ≤ 3 * ((k : ℝ) * (Real.log k + Real.log k + (20 * k) * Real.log k)) := by
      gcongr
    _ = (6 * k + 60 * (k : ℝ) ^ 2) * Real.log k := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hl0
      nlinarith

lemma binaryLength_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ binaryLength k := by
  have hM := wordLength_upper_start hk
  calc
    k ≤ wordLength k := hM
    _ = wordLength k ^ 1 := by simp
    _ ≤ binaryLength k := pow_le_pow_right₀ (by omega) (by omega)

end FiniteTree

theorem binary_finite : BinaryLowerBound := by
  apply all_caps_of_witnesses (N := FiniteTree.binaryLength) (A := 100) (by norm_num)
  filter_upwards [FiniteTree.witnesses_eventually,
    eventually_exponential_lower (b := 4) (C := 32160) (by norm_num) (by norm_num) 0,
    Filter.eventually_ge_atTop 20] with k hw he hk
  obtain ⟨W, hW, hlen, hD⟩ := hw
  refine ⟨FiniteTree.binaryLength_ge (by omega), FiniteTree.length_log_bound hk,
    W, hW, hlen, ?_⟩
  simp only [pow_zero, mul_one] at he
  exact he.trans hD

end TreeEdit

end OAI
