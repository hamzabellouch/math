import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialTripling

namespace OAI

/-! # Two separated scales with controlled growth

The multiplicative form of Kleiner's good-scale argument, Section 3.1.
-/
namespace PolycyclicRecognition

theorem exists_adjacent_ratio_of_block_bound (v : ℕ → ℝ) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 0 < n) (hbound : v n ≤ A ^ n * v 0) :
    ∃ i < n, v (i + 1) ≤ A * v i := by
  by_contra! h
  have hstep : ∀ k, 0 < k → k ≤ n → A ^ k * v 0 < v k := by
    intro k
    induction k with
    | zero => intro hk _; omega
    | succ k ih =>
      intro _ hk
      by_cases he : k = 0
      · subst k
        simpa using h 0 (by omega)
      · calc
          A ^ (k + 1) * v 0 = A * (A ^ k * v 0) := by rw [pow_succ]; ring
          _ < A * v k := mul_lt_mul_of_pos_left (ih (Nat.pos_of_ne_zero he) (by omega)) hA
          _ < v (k + 1) := h k (by omega)
  exact (hstep n hn le_rfl).not_ge hbound

theorem two_good_scales_of_block_bound (v : ℕ → ℝ) (hv : Monotone v)
    {A : ℝ} (hA : 0 < A) (m w : ℕ) (hw : 0 < w)
    (hb : v (m + 3 * w) ≤ A ^ w * v m) :
    ∃ i j : ℕ, m ≤ i ∧ i < m + w ∧ m + 2 * w ≤ j ∧ j < m + 3 * w ∧
      w < j - i ∧ j - i < 3 * w ∧
      v (i + 1) ≤ A * v i ∧ v (j + 1) ≤ A * v j ∧ v (j + 1) ≤ A ^ w * v i := by
  have hfirst : v (m + w) ≤ A ^ w * v m := (hv (by omega)).trans hb
  have hlast : v (m + 2 * w + w) ≤ A ^ w * v (m + 2 * w) := by
    calc
      _ = v (m + 3 * w) := by congr 1; omega
      _ ≤ A ^ w * v m := hb
      _ ≤ A ^ w * v (m + 2 * w) := mul_le_mul_of_nonneg_left (hv (by omega)) (pow_pos hA w).le
  obtain ⟨i, hi, hvi⟩ := exists_adjacent_ratio_of_block_bound (fun k => v (m + k)) hA hw
    (by simpa only [Nat.add_zero] using hfirst)
  obtain ⟨j, hj, hvj⟩ := exists_adjacent_ratio_of_block_bound (fun k => v (m + 2 * w + k)) hA hw
    (by simpa only [Nat.add_zero] using hlast)
  refine ⟨m + i, m + 2 * w + j, by omega, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hvi
  · simpa only [Nat.add_assoc] using hvj
  · exact ((hv (by omega)).trans hb).trans
      (mul_le_mul_of_nonneg_left (hv (by omega)) (pow_pos hA w).le)

theorem exponential_growth_two_good_scales (v : ℕ → ℝ)
    (hv : Monotone v) (hpos : ∀ n, 0 < v n) {C B : ℝ} (hB : 0 < B)
    (hbound : ∀ n, v n ≤ C * B ^ n) (R w : ℕ) (hw : 0 < w) :
    let A := 2 * B ^ 3
    ∃ i j : ℕ, R ≤ i ∧ w < j - i ∧ j - i < 3 * w ∧
      v (i + 1) ≤ A * v i ∧ v (j + 1) ≤ A * v j ∧ v (j + 1) ≤ A ^ w * v i := by
  let A := 2 * B ^ 3
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 2 * B ^ (3 * w) ≤ A ^ w := by
    have hw' : (2 : ℝ) ≤ 2 ^ w := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hw
    calc
      _ ≤ 2 ^ w * B ^ (3 * w) := mul_le_mul_of_nonneg_right hw' (pow_pos hB _).le
      _ = A ^ w := by dsimp only [A]; rw [mul_pow, ← pow_mul]
  obtain ⟨n, hn⟩ := exists_geometric_growth_ratio (fun k => v (R + 3 * w * k))
    (C := C * B ^ R) (B := B ^ (3 * w)) (pow_pos hB _)
    (fun k => (hpos _).le) (by simpa using hpos R) (by
      intro k
      calc
        _ ≤ C * B ^ (R + 3 * w * k) := hbound _
        _ = (C * B ^ R) * (B ^ (3 * w)) ^ k := by rw [pow_add, pow_mul]; ring)
  have hb : v (R + 3 * w * n + 3 * w) ≤ A ^ w * v (R + 3 * w * n) := by
    have he : R + 3 * w * (n + 1) = R + 3 * w * n + 3 * w := by ring
    rw [he] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right hc (hpos _).le)
  obtain ⟨i, j, hi, _, _, _, hgap, hgap', hvi, hvj, hvij⟩ :=
    two_good_scales_of_block_bound v hv hA (R + 3 * w * n) w hw hb
  exact ⟨i, j, (by omega), hgap, hgap', hvi, hvj, hvij⟩

end PolycyclicRecognition

end OAI
