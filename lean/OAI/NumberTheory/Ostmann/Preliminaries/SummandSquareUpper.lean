import OAI.NumberTheory.Ostmann.Preliminaries.SummandPolynomialLower

namespace OAI

/-! # The square-root upper bound at square endpoints -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_square_upper {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : ℕ in atTop,
      ((summandPrefix A (q ^ 2)).card : ℝ) ≤ C * q * Real.log (q : ℝ) ^ 2 := by
  obtain ⟨N₀, hcomp⟩ := h.summand_square_comparison hB.nonempty
  refine ⟨N₀ + 19203, by positivity, ?_⟩
  have htend : Tendsto (fun q : ℕ => q ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hloglarge := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hcomp, htend.eventually (h.symm.summand_polynomial_lower hB),
    hloglarge, eventually_ge_atTop (3 : ℕ)] with q hc hp hl hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  change 1 ≤ Real.log (q : ℝ) at hl
  have hp' : (q : ℝ) ^ 6 ≤ ((summandPrefix B (q ^ 24)).card : ℝ) := by
    simpa only [← pow_mul, Nat.cast_pow] using hp
  have h3q : 3 * (q : ℝ) ≤ (q : ℝ) ^ 6 := by
    have hq5 : (q : ℝ) ≤ (q : ℝ) ^ 5 := le_self_pow₀ hq1 (by norm_num)
    have h3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    calc
      _ ≤ (q : ℝ) ^ 5 * q := mul_le_mul_of_nonneg_right (h3.trans hq5) hqp.le
      _ = _ := by ring
  have hbp : (0 : ℝ) < (summandPrefix B (q ^ 24)).card := (by positivity : 0 < (q : ℝ) ^ 6).trans_le hp'
  have hbne : (summandPrefix B (q ^ 24)).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hbp)
  have hfrac : 3 * (q : ℝ) / ((summandPrefix B (q ^ 24)).card : ℝ) ≤ 1 :=
    (div_le_iff₀ hbp).mpr (by simpa using h3q.trans hp')
  have hlog2 : Real.log (2 * (q : ℝ)) ≤ 2 * Real.log (q : ℝ) := by
    rw [Real.log_mul (by norm_num) hqp.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ q by exact_mod_cast (by omega : 2 ≤ q))
    linarith
  have hlogY : Real.log ((q ^ 24 : ℕ) : ℝ) +
      3 * (q : ℝ) / ((summandPrefix B (q ^ 24)).card : ℝ) ≤ 25 * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  have hbound := hc (q ^ 24) (one_le_pow₀ (by omega : 1 ≤ q)) hbne
  have hmain : 384 * (q : ℝ) * Real.log (2 * (q : ℝ)) *
      (Real.log ((q ^ 24 : ℕ) : ℝ) +
        3 * (q : ℝ) / ((summandPrefix B (q ^ 24)).card : ℝ)) ≤
          19200 * q * Real.log (q : ℝ) ^ 2 := by
    calc
      _ ≤ 384 * (q : ℝ) * (2 * Real.log (q : ℝ)) * (25 * Real.log (q : ℝ)) := by
        gcongr
      _ = _ := by ring
  have hlogSq : 1 ≤ Real.log (q : ℝ) ^ 2 := by nlinarith
  have hboundary : (N₀ : ℝ) + 2 * q + 1 ≤
      (N₀ + 3 : ℝ) * q * Real.log (q : ℝ) ^ 2 := by
    calc
      _ ≤ (N₀ + 3 : ℝ) * q := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N₀) (sub_nonneg.mpr hq1)]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hlogSq
  have hh := hbound.trans (add_le_add_right hmain _)
  nlinarith [hboundary]

end Ostmann

end OAI
