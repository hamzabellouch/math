import Mathlib

namespace OAI

/-!
# Arithmetic for the finite-tree obstruction

The parameter estimate and final rearrangement in `prop:finite-lower` hold
with the explicit absolute constant 34.
-/

namespace TreeEdit.BinaryLower.FiniteNumeric

lemma period_ratio_bound {k : ℕ} (hk : 1 ≤ k) :
    2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) / (k : ℝ) ^ (20 * k)
      ≤ 8 / (k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 < (k : ℝ) ^ (10 * k) := pow_pos hk0 _
  have hb : 0 < (k : ℝ) ^ k := pow_pos hk0 _
  have hp : (k : ℝ) * (k : ℝ) ^ k ≤ (k : ℝ) ^ (10 * k) := by
    calc
      (k : ℝ) * (k : ℝ) ^ k = (k : ℝ) ^ (k + 1) := by ring
      _ ≤ (k : ℝ) ^ (10 * k) :=
        pow_le_pow_right₀ hk1 (by omega)
  have ht : (k : ℝ) ^ (20 * k) = ((k : ℝ) ^ (10 * k)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [ht]
  have hs : 2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) /
      ((k : ℝ) ^ (10 * k)) ^ 2 = 8 * (k : ℝ) / (k : ℝ) ^ (10 * k) := by
    field_simp
    ring
  rw [hs]
  apply (div_le_div_iff₀ ha hb).2
  nlinarith

/-- The final line of `eq:finite-root-upper`, with an explicit constant. -/
theorem finite_root_bound {k : ℕ} {M V : ℝ} (hk : 1 ≤ k) (hM : 0 ≤ M)
    (hV : V ≤ 4 * M *
      (2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) / (k : ℝ) ^ (20 * k) +
        1 / (2 * (k : ℝ) ^ k))) :
    V ≤ 34 * M / (k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp : (k : ℝ) ^ k ≠ 0 := ne_of_gt (pow_pos hk0 _)
  calc
    V ≤ 4 * M *
      (2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) / (k : ℝ) ^ (20 * k) +
        1 / (2 * (k : ℝ) ^ k)) := hV
    _ ≤ 4 * M * (8 / (k : ℝ) ^ k + 1 / (2 * (k : ℝ) ^ k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [period_ratio_bound hk]
    _ = 34 * M / (k : ℝ) ^ k := by field_simp; ring

/-- Uniform root separation and the preceding upper displacement estimate
force the source's `(k/4)^k` lower distortion, with constant `1/34`. -/
theorem finite_distortion_bound {k : ℕ} {M V D : ℝ}
    (hk : 1 ≤ k) (hM : 0 < M) (hD : 0 < D)
    (hlower : M / ((4 : ℝ) ^ k * D) ≤ V)
    (hupper : V ≤ 34 * M / (k : ℝ) ^ k) :
    ((k : ℝ) / 4) ^ k / 34 ≤ D := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp : 0 < (k : ℝ) ^ k := pow_pos hk0 _
  have hfour : 0 < (4 : ℝ) ^ k := by positivity
  have hcompare := hlower.trans hupper
  have hcross := (div_le_div_iff₀ (mul_pos hfour hD) hp).1 hcompare
  have hcancel : (k : ℝ) ^ k ≤ 34 * (4 : ℝ) ^ k * D := by
    apply (mul_le_mul_iff_of_pos_left hM).1
    nlinarith [hcross]
  rw [div_pow, div_div]
  apply (div_le_iff₀ (mul_pos hfour (by norm_num : (0 : ℝ) < 34))).2
  nlinarith [hcancel]

/-- The source averaging length `J=4k^(10k)` lies within the row budget
`T=k^(20k)` already for every `k≥2`. -/
theorem averaging_length_le_rows {k : ℕ} (hk : 2 ≤ k) :
    4 * k ^ (10 * k) ≤ k ^ (20 * k) := by
  have hfour : 4 ≤ k ^ (10 * k) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
      _ ≤ k ^ (10 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    4 * k ^ (10 * k) ≤ k ^ (10 * k) * k ^ (10 * k) :=
      Nat.mul_le_mul_right _ hfour
    _ = k ^ (20 * k) := by rw [← pow_add]; congr 1; omega

/-- The bound on a sparse character period at any internal depth implies the
half-averaging-interval bound required by short-period detection. -/
theorem sparse_period_twice_le {k j r q : ℕ} (hk : 1 ≤ k)
    (hj : j < k) (hr : r < k)
    (hq : q ≤ 2 * k ^ (5 * j + 5 * r)) :
    2 * q ≤ 4 * k ^ (10 * k) := by
  have hp : k ^ (5 * j + 5 * r) ≤ k ^ (10 * k) :=
    Nat.pow_le_pow_right hk (by omega)
  nlinarith

end TreeEdit.BinaryLower.FiniteNumeric

end OAI
