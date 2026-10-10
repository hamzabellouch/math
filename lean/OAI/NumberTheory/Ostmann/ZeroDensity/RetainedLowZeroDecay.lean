import OAI.NumberTheory.Ostmann.ZeroDensity.LowZeroDecayRate

namespace OAI

/-! # Uniform low-zero decay in the manuscript's conductor range -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem retained_low_zero_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (a D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q →
      Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) → (∀ χ ∈ F, some χ ≠ exception) →
        (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices ((Q : ℝ) ^ 5)).filter
          (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
            Real.exp (-Real.exp L * (1 - ((Z χ).zeros i).re))) ≤ Real.exp (-D * L) := by
  obtain ⟨C, c, _, hc, hzero⟩ := retained_low_zero_estimate Z hD hR
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (84 * a)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventual_low_zero_error C c a D hc ha, hsmall,
    eventually_ge_atTop (1 : ℝ)] with L herr hsmall hL
  intro Q hQ hQL
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQp : (0 : ℝ) < Q := by linarith
  have hT : (2 : ℝ) ≤ (Q : ℝ) ^ 5 := by
    calc
      2 ≤ (Q : ℝ) := by exact_mod_cast (show 2 ≤ Q by omega)
      _ ≤ (Q : ℝ) * (Q : ℝ) ^ 4 :=
        le_mul_of_one_le_right hQp.le (one_le_pow₀ hQr)
      _ = _ := by ring
  have hlogQT : Real.log ((Q : ℝ) * (Q : ℝ) ^ 5) = 6 * Real.log Q := by
    rw [Real.log_mul hQp.ne' (pow_ne_zero _ hQp.ne'), Real.log_pow]
    ring
  have hlogQ2T : Real.log ((Q : ℝ) ^ 2 * (Q : ℝ) ^ 5) = 7 * Real.log Q := by
    rw [Real.log_mul (pow_ne_zero _ hQp.ne') (pow_ne_zero _ hQp.ne'), Real.log_pow,
      Real.log_pow]
    ring
  have hlog2QT : Real.log (2 * (Q : ℝ) * (Q : ℝ) ^ 5) =
      Real.log 2 + 6 * Real.log Q := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) hQp.ne') (pow_ne_zero _ hQp.ne'),
      Real.log_mul (by norm_num) hQp.ne', Real.log_pow]
    ring
  have hg : 84 * a * L ≤ Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 84 * a * L),
      abs_of_pos (Real.exp_pos _), one_mul] using hsmall
  have hM : 12 * Real.log ((Q : ℝ) ^ 2 * (Q : ℝ) ^ 5) ≤ Real.exp L := by
    rw [hlogQ2T]
    have hm := mul_le_mul_of_nonneg_right hg (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    have he : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) =
        Real.exp L := by rw [← Real.exp_add]; congr 1; ring
    rw [he] at hm
    linarith
  obtain ⟨exception, he⟩ := hzero Q hQ ((Q : ℝ) ^ 5) hT
  refine ⟨exception, ?_⟩
  intro F hF hFE
  have hh := he F hF hFE (Real.exp L) hM
  rw [hlogQT, hlog2QT] at hh
  exact hh.trans (herr (Real.log Q) (Real.log_nonneg hQr) hQL)

end Ostmann

end OAI
