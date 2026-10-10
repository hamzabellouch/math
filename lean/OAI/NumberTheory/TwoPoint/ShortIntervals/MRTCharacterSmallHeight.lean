import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterGlobalTail
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvilleLSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! A concrete low-height range in the original Liouville prime tail.
Only nonprincipal characters are covered here. -/

namespace TwoPointCorrelations

open Filter Finset
open scoped Classical

lemma mrt_prime_power_cutoff_log_lower {a : ℝ} (ha : 0 < a) :
    ∀ᶠ X : ℕ in atTop,
      (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ a ≤
        Real.log (mrtPrimePowerCutoff a X : ℝ) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := ((tendsto_rpow_atTop ha).comp hlog).eventually
    (eventually_ge_atTop (max 2 (2 * Real.log 2)))
  filter_upwards [hp] with X hX
  let A := (Real.log (X : ℝ)) ^ a
  have hA : 2 ≤ A := (le_max_left _ _).trans hX
  have hAl : 2 * Real.log 2 ≤ A := (le_max_right _ _).trans hX
  have hE : 2 ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
  have hf : Real.exp A / 2 ≤ (mrtPrimePowerCutoff a X : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp A)
    change Real.exp A / 2 ≤ (⌊Real.exp A⌋₊ : ℝ)
    linarith
  have hf0 : 0 < (mrtPrimePowerCutoff a X : ℝ) :=
    (div_pos (Real.exp_pos A) (by norm_num)).trans_le hf
  have hh := Real.log_le_log (div_pos (Real.exp_pos A) (by norm_num)) hf
  rw [Real.log_div (Real.exp_pos A).ne' (by norm_num), Real.log_exp] at hh
  change (1 / 2 : ℝ) * A ≤ _
  linarith

lemma mrt_character_small_height_bound {q : ℕ} [NeZero q] {L t : ℝ}
    (hL : 1 ≤ L) (hq : (q : ℝ) ≤ L ^ (1 / 125 : ℝ))
    (ht : |t| ≤ Real.exp (L ^ (1 / 3 : ℝ)))
    (hlog : Real.log L ≤ L ^ (1 / 3 : ℝ))
    (hthree : Real.log 3 ≤ L ^ (1 / 3 : ℝ)) :
    mrtCharacterHeight q t ≤ 3 * L ^ (1 / 3 : ℝ) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hqp : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hlogq := Real.log_le_log hqp hq
  rw [Real.log_rpow hL0] at hlogq
  have hE : 1 ≤ Real.exp (L ^ (1 / 3 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have he : |t| + 2 ≤ 3 * Real.exp (L ^ (1 / 3 : ℝ)) := by linarith
  have hl := Real.log_le_log (by positivity : 0 < |t| + 2) he
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hl
  rw [mrt_character_height_split]
  have hpow : 0 ≤ L ^ (1 / 3 : ℝ) := Real.rpow_nonneg hL0.le _
  linarith

lemma mrt_character_small_height_cost : ∀ᶠ L : ℝ in atTop,
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L ^ (1 / 125 : ℝ) →
    ∀ t : ℝ, |t| ≤ Real.exp (L ^ (1 / 3 : ℝ)) →
      (q : ℝ) ^ 2 * mrtCharacterHeight q t ^ 2 ≤ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) := by
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hp := (tendsto_rpow_atTop (show (0 : ℝ) < 101 / 1500 by norm_num)).eventually
    (eventually_ge_atTop (18 : ℝ))
  have hthree := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).eventually
    (eventually_ge_atTop (Real.log 3))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl, hp, hthree] with L hL hl hp hthree
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL0 _), one_mul] at hl
  intro q _ hq t ht
  have hh := mrt_character_small_height_bound hL hq ht hl hthree
  have hH := (mrt_character_height_pos q t).le
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hm := mul_le_mul (pow_le_pow_left₀ hq0 hq 2) (pow_le_pow_left₀ hH hh 2)
    (sq_nonneg _) (by positivity : 0 ≤ (L ^ (1 / 125 : ℝ)) ^ 2)
  have h₁ : (L ^ (1 / 125 : ℝ)) ^ 2 = L ^ (2 / 125 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
  have h₂ : (L ^ (1 / 3 : ℝ)) ^ 2 = L ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
  have he : (L ^ (1 / 125 : ℝ)) ^ 2 * (3 * L ^ (1 / 3 : ℝ)) ^ 2 =
      9 * L ^ (256 / 375 : ℝ) := by
    calc
      _ = 9 * (L ^ (2 / 125 : ℝ) * L ^ (2 / 3 : ℝ)) := by rw [mul_pow, h₁, h₂]; ring
      _ = _ := by rw [← Real.rpow_add hL0]; norm_num

  rw [he] at hm
  have hmul := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hL0.le (256 / 375))
  have hsum : L ^ (101 / 1500 : ℝ) * L ^ (256 / 375 : ℝ) = L ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  rw [hsum] at hmul
  linarith

theorem mrt_liouville_nonprincipal_small_height : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ,
        |t| ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 / 3 : ℝ)) →
        |(∑ p ∈ mrtLiouvillePrimeTail X, characterTwist χ t p / (p : ℂ)).re| ≤ C := by
  obtain ⟨C, hC, htail⟩ := mrt_character_global_prime_tail
  refine ⟨C, hC, ?_⟩
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually mrt_character_small_height_cost,
    mrt_prime_power_cutoff_log_lower (show (0 : ℝ) < 3 / 4 by norm_num),
    mrt_prime_power_cutoff_eventually (show (0 : ℝ) < 3 / 4 by norm_num) (by norm_num)]
    with X hcost hlower hcut
  intro q hq hqX χ hχ t ht
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  change |(∑ p ∈ mrtPrimePowerTail (3 / 4) X, characterTwist χ t p / (p : ℂ)).re| ≤ C
  rw [mrt_prime_power_tail_cutoff]
  exact htail q χ hχ t _ _ hcut.1 hcut.2 ((hcost q hqX t ht).trans hlower)

end TwoPointCorrelations

end OAI
