import OAI.NumberTheory.Ostmann.Preliminaries.SummandSizeFiniteInequality
import OAI.NumberTheory.Ostmann.Preliminaries.SummandSizePrimeBand
import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftInitialSegment

namespace OAI

/-! # A two-cutoff comparison at square endpoints -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

private theorem square_comparison_algebra (q L m c H : ℝ)
    (hq : 1 ≤ q) (hL : 0 < L) (hm : 0 ≤ m) (_hc : 0 ≤ c) (hH : 0 ≤ H)
    (hcount : q / (4 * L) ≤ c)
    (hineq : m * (L / 2 * c ^ 2) ≤ 2 * q * (q ^ 2 + 1 + (2 * q) ^ 2) * H) :
    m ≤ 384 * q * L * H := by
  have hqc : q ≤ 4 * L * c := by
    have hh := (div_le_iff₀ (by positivity : 0 < 4 * L)).mp hcount
    nlinarith
  have hsq : q ^ 2 ≤ 16 * L ^ 2 * c ^ 2 := by nlinarith
  have hmsq := mul_le_mul_of_nonneg_left hsq hm
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hupper : m * (L / 2 * c ^ 2) ≤ 12 * q ^ 3 * H := by
    apply hineq.trans
    nlinarith [mul_nonneg (sub_nonneg.mpr hq2) (mul_nonneg (by linarith : 0 ≤ q) hH)]
  have hscaled := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 32 * L by positivity)
  have hfinal : q ^ 2 * m ≤ q ^ 2 * (384 * q * L * H) := by nlinarith [hmsq, hscaled]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < q ^ 2)).mp hfinal

 theorem EventuallyPrimeSumset.summand_square_comparison {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Nonempty) :
    ∃ N₀ : ℕ, ∀ᶠ q : ℕ in atTop, ∀ Y : ℕ, 1 ≤ Y →
      (summandPrefix B Y).Nonempty →
      ((summandPrefix A (q ^ 2)).card : ℝ) ≤ N₀ + 2 * q + 1 +
        384 * q * Real.log (2 * (q : ℝ)) *
          (Real.log (Y : ℝ) + 3 * q / ((summandPrefix B Y).card : ℝ)) := by
  obtain ⟨N₀, hN⟩ := h.summand_size_finite_inequality hB
  refine ⟨N₀, ?_⟩
  filter_upwards [sizePrimeBand_eventual_bounds] with q hq
  intro Y hY hBY
  let L := Real.log (2 * (q : ℝ))
  let H := Real.log (Y : ℝ) + 3 * q / ((summandPrefix B Y).card : ℝ)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (Real.log_nonneg (by exact_mod_cast hY)) (by positivity)
  have htail : ((summandTail A (N₀ + 2 * q) (q ^ 2)).card : ℝ) ≤
      384 * q * L * H := by
    by_cases hu : (summandTail A (N₀ + 2 * q) (q ^ 2)).Nonempty
    · have he : L / 2 ≤ Real.log (q : ℝ) := by
        have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ q by exact_mod_cast hq.1)
        dsimp [L]
        rw [Real.log_mul (by norm_num) hqp.ne']
        linarith
      have hh := hN (q ^ 2) (2 * q) Y (sizePrimeBand q) (L / 2)
        (by omega) hY (by positivity)
        (fun p hp => (mem_sizePrimeBand.mp hp).1)
        (fun p hp => (mem_sizePrimeBand.mp hp).2.2)
        (fun p hp => he.trans (Real.log_le_log hqp
          (by exact_mod_cast (mem_sizePrimeBand.mp hp).2.1.le))) hu hBY
      have hmass : Real.log (Y : ℝ) +
          (1 / ((summandPrefix B Y).card : ℝ)) *
            (∑ p ∈ sizePrimeBand q, Real.log (p : ℝ)) ≤ H := by
        have hh := mul_le_mul_of_nonneg_left hq.2.2
          (show 0 ≤ 1 / ((summandPrefix B Y).card : ℝ) by positivity)
        dsimp [H]
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc, add_comm] using add_le_add_left hh (Real.log (Y : ℝ))
      have hi : ((summandTail A (N₀ + 2 * q) (q ^ 2)).card : ℝ) *
          (L / 2 * ((sizePrimeBand q).card : ℝ) ^ 2) ≤
          2 * q * ((q : ℝ) ^ 2 + 1 + (2 * q) ^ 2) * H := by
        push_cast at hh
        exact hh.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
      exact square_comparison_algebra q L _ _ H hq1 hL (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hH hq.2.1 hi
    · rw [Finset.not_nonempty_iff_eq_empty.mp hu, Finset.card_empty, Nat.cast_zero]
      positivity
  have hc : ((summandPrefix A (q ^ 2)).card : ℝ) ≤
      (N₀ : ℝ) + 2 * q + 1 + ((summandTail A (N₀ + 2 * q) (q ^ 2)).card : ℝ) := by
    exact_mod_cast summandPrefix_card_le_initial_add_tail A (N₀ + 2 * q) (q ^ 2)
  exact hc.trans (add_le_add_right htail _)

end Ostmann

end OAI
