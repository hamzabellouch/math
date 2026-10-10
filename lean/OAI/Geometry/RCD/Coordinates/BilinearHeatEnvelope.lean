import OAI.Geometry.RCD.Heat.SlowHeatGrowth
import OAI.Geometry.RCD.Coordinates.SymmetricDomination

namespace OAI

/-! # From a scalar source envelope to the bilinear heat comparison -/

open scoped BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

theorem geometric_causal_sum_succ (f : ℕ → ℝ) (β : ℝ) (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1 + 1), β ^ (i + 1 - j) * f j) =
      β * (∑ j ∈ Finset.range (i + 1), β ^ (i - j) * f j) + f (i + 1) := by
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  rw [show i + 1 - j = (i - j) + 1 by omega, pow_succ]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual geometric source envelope is bounded by the current heat
metric under slow growth and small mass. Its finite background is explicit. -/
theorem heat_envelope_le_current (Q N F : ℕ → E →L[ℝ] E)
    (hQ : ∀ i, (Q i).IsPositive) {b T ε : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hstep : ∀ i v, ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ)
    (hbase : ∀ v, ‖v‖ ^ 2 ≤ T * ⟪v, Q 0 v⟫_ℝ)
    (hsmall : ∀ i v, ⟪v, N i v⟫_ℝ ≤ ε * ⟪v, Q i v⟫_ℝ)
    (henv : ∀ i v, ⟪v, F i v⟫_ℝ ≤ b * (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) * ⟪v, N j v⟫_ℝ)
    (i : ℕ) (v : E) :
    ⟪v, F i v⟫_ℝ ≤ (b * T + 8 * ε) * ⟪v, Q i v⟫_ℝ := by
  have hmass : ∀ i, (∑ j ∈ Finset.range (i + 1),
      (3 / 4 : ℝ) ^ (i - j) * ⟪v, N j v⟫_ℝ) ≤ 8 * ε * ⟪v, Q i v⟫_ℝ := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_self, pow_zero, one_mul]
      have hn := hsmall 0 v
      have hp := (hQ 0).inner_nonneg_right v
      nlinarith only [hn, mul_nonneg hε hp]
    | succ k ih =>
      rw [geometric_causal_sum_succ]
      have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 3 / 4)
      have ht := mul_le_mul_of_nonneg_left (hstep k v) (by positivity : 0 ≤ (3 / 4 : ℝ) * (8 * ε))
      have hn := hsmall (k + 1) v
      have hp := (hQ (k + 1)).inner_nonneg_right v
      nlinarith only [hm, ht, hn, mul_nonneg hε hp]
  have hg := geometric_form_growth Q (by norm_num : (0 : ℝ) ≤ 9 / 8) hstep (Nat.zero_le i) v
  simp only [Nat.sub_zero] at hg
  have hinit := mul_le_mul_of_nonneg_left ((hbase v).trans (mul_le_mul_of_nonneg_left hg hT))
    (by positivity : 0 ≤ b * (3 / 4 : ℝ) ^ i)
  have hpow : (3 / 4 : ℝ) ^ i * (9 / 8 : ℝ) ^ i ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpow' := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hb hT) ((hQ i).inner_nonneg_right v))
  have hinitial : b * (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 ≤ b * T * ⟪v, Q i v⟫_ℝ := by
    nlinarith only [hinit, hpow']
  nlinarith only [henv i v, hmass i, hinitial]

/-- Once the signed scalar source estimate is proved, polarization gives
exactly the asymmetric bilinear estimate required by the coordinate argument. -/
theorem bilinear_heat_comparison_of_envelope (Q F D : E →L[ℝ] E)
    (hF : F.IsPositive) (hD : D.IsSymmetric) {C B : ℝ}
    (hsource : ∀ v, |⟪v, D v⟫_ℝ| ≤ C * ⟪v, F v⟫_ℝ)
    (hcurrent : ∀ v, ⟪v, F v⟫_ℝ ≤ B * ⟪v, Q v⟫_ℝ) (v w : E) :
    ⟪v, D w⟫_ℝ ^ 2 ≤ (C ^ 2 * B) * ⟪v, Q v⟫_ℝ * ⟪w, F w⟫_ℝ := by
  have hd : ∀ u, |⟪u, D u⟫_ℝ| ≤ ⟪u, (C • F) u⟫_ℝ := by
    intro u
    simpa only [smul_apply, inner_smul_right] using hsource u
  have h := symmetric_domination_cauchy_schwarz D (C • F) hD hd v w
  simp only [smul_apply, inner_smul_right] at h
  have hs := mul_le_mul_of_nonneg_right (hcurrent v)
    (mul_nonneg (sq_nonneg C) (hF.inner_nonneg_right w))
  nlinarith only [h, hs]

end RegularPointCoordinates

end

end OAI
