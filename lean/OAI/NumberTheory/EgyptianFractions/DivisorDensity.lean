import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- A positive integer has a divisor within a factor of `m` below each scale. -/
def DivisorDense (m q : ℕ) : Prop :=
  ∀ w : ℝ, 1 ≤ w → w ≤ (q : ℝ) →
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ w / (m : ℝ) ≤ (d : ℝ) ∧ (d : ℝ) ≤ w

theorem divisorDense_base {m : ℕ} (hm : 2 ≤ m) : DivisorDense m m := by
  intro w hw hwm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨1, by omega, one_dvd m, ?_, ?_⟩
  · simpa using (div_le_iff₀ hmpos).2 (by simpa using hwm)
  · simpa using hw

theorem DivisorDense.mul {m q n : ℕ} (hq : DivisorDense m q)
    (hm : 2 ≤ m) (hqpos : 1 ≤ q) (hnpos : 1 ≤ n) (hn : n ≤ q + 1) :
    DivisorDense m (n * q) := by
  intro w hw hwnq
  have hmposR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnposR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqposR : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (n : ℝ) ≤ q + 1 := by exact_mod_cast hn
  simp only [Nat.cast_mul] at hwnq
  by_cases hwq : w ≤ (q : ℝ)
  · obtain ⟨d, hdpos, hdq, hdl, hdu⟩ := hq w hw hwq
    exact ⟨d, hdpos, dvd_mul_of_dvd_right hdq n, hdl, hdu⟩
  · by_cases hnw : (n : ℝ) ≤ w
    · have hwdiv : 1 ≤ w / (n : ℝ) := by
        exact (le_div_iff₀ hnposR).2 (by simpa using hnw)
      have hwdivq : w / (n : ℝ) ≤ q := by
        apply (div_le_iff₀ hnposR).2
        nlinarith [hwnq]
      obtain ⟨d, hdpos, hdq, hdl, hdu⟩ := hq (w / n) hwdiv hwdivq
      refine ⟨n * d, Nat.mul_pos (by omega) hdpos, Nat.mul_dvd_mul_left n hdq, ?_, ?_⟩
      · have hdl' : w / (n : ℝ) ≤ (d : ℝ) * m := (div_le_iff₀ hmposR).1 hdl
        have hdl'' : w ≤ (d : ℝ) * m * n := (div_le_iff₀ hnposR).1 hdl'
        apply (div_le_iff₀ hmposR).2
        simp only [Nat.cast_mul]
        nlinarith [hdl'']
      · have hdu' : (d : ℝ) * n ≤ w := (le_div_iff₀ hnposR).1 hdu
        simpa only [Nat.cast_mul, mul_comm] using hdu'
    · refine ⟨q, by omega, dvd_mul_left q n, ?_, by linarith⟩
      apply (div_le_iff₀ hmposR).2
      nlinarith

/-- Denominators produced by multiplying by positive integers at most one
more than the preceding denominator, without reducing fractions. -/
inductive GreedyDenominator (m : ℕ) : ℕ → Prop
  | base : GreedyDenominator m m
  | mul {q n : ℕ} : GreedyDenominator m q → 1 ≤ n → n ≤ q + 1 →
      GreedyDenominator m (n * q)

theorem GreedyDenominator.positive {m q : ℕ} (h : GreedyDenominator m q)
    (hm : 1 ≤ m) : 1 ≤ q := by
  induction h with
  | base => exact hm
  | @mul q n h hn hnq ih => exact Nat.mul_pos hn ih

theorem GreedyDenominator.divisorDense {m q : ℕ} (h : GreedyDenominator m q)
    (hm : 2 ≤ m) : DivisorDense m q := by
  induction h with
  | base => exact divisorDense_base hm
  | @mul q n h hn hnq ih =>
      exact ih.mul hm (h.positive (by omega)) hn hnq

theorem marked_divisor_density {m q : ℕ} (hm : 2 ≤ m)
    (hq : GreedyDenominator m q) {w : ℝ} (hw : 1 ≤ w) (hwq : w ≤ (q : ℝ)) :
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ w / (m : ℝ) ≤ (d : ℝ) ∧ (d : ℝ) ≤ w :=
  hq.divisorDense hm w hw hwq

end Problem337

end

end OAI
