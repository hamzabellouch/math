import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCosineLower
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterSmallHeight
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvillePrimitive

namespace OAI

/-! The principal character in the low-height Liouville prime-tail range,
from the proved prime-number theorem and a uniform cosine integral bound. -/

namespace TwoPointCorrelations

open Filter Finset
open scoped Classical Topology

lemma mrt_small_height_phase_error (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, |t| ≤ Real.exp (L ^ (1 / 3 : ℝ)) →
      (8 + |t|) * K * Real.exp (-c * L ^ (3 / 8 : ℝ)) / L ^ (3 / 4 : ℝ) ≤ 1 := by
  have hg := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 24 by norm_num)).eventually
    (eventually_ge_atTop (2 / c))
  have hd := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (c / 2) (by positivity)).comp
    (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 8 by norm_num))
  simp only [Real.rpow_zero, one_mul] at hd
  have hd' : Tendsto (fun L : ℝ => 9 * K * Real.exp (-(c / 2) * L ^ (3 / 8 : ℝ)))
      atTop (𝓝 0) := by simpa using hd.const_mul (9 * K)
  have he := hd'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hg, he] with L hL hg he
  intro t ht
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hsum : L ^ (1 / 3 : ℝ) * L ^ (1 / 24 : ℝ) = L ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hL0.le (1 / 3))
  rw [hsum] at hm
  have hsmall : L ^ (1 / 3 : ℝ) ≤ (c / 2) * L ^ (3 / 8 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ c / 2 by positivity)
    have heq : (c / 2) * (L ^ (1 / 3 : ℝ) * (2 / c)) = L ^ (1 / 3 : ℝ) := by field_simp
    rw [heq] at hh
    exact hh
  have hexp : Real.exp (L ^ (1 / 3 : ℝ)) * Real.exp (-c * L ^ (3 / 8 : ℝ)) ≤
      Real.exp (-(c / 2) * L ^ (3 / 8 : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hone : 1 ≤ Real.exp (L ^ (1 / 3 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hmain : (8 + |t|) * K * Real.exp (-c * L ^ (3 / 8 : ℝ)) ≤
      9 * K * Real.exp (-(c / 2) * L ^ (3 / 8 : ℝ)) := by
    calc
      _ ≤ (9 * Real.exp (L ^ (1 / 3 : ℝ))) * K * Real.exp (-c * L ^ (3 / 8 : ℝ)) := by
        gcongr
        linarith
      _ = (9 * K) * (Real.exp (L ^ (1 / 3 : ℝ)) * Real.exp (-c * L ^ (3 / 8 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hden : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL (by norm_num)
  exact (div_le_self (by positivity) hden).trans (hmain.trans he.le)

lemma mrt_principal_twist_re {q : ℕ} (hq : 0 < q) {p : ℕ}
    (hp : p.Prime) (hqp : q < p) (t : ℝ) :
    (characterTwist (1 : DirichletCharacter ℂ q) t p).re = Real.cos (t * Real.log (p : ℝ)) := by
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact (not_le_of_gt hqp) (Nat.le_of_dvd hq h))
  have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hcop
  unfold characterTwist
  rw [MulChar.one_apply hu, one_mul, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    sub_zero, Real.exp_zero, one_mul]

theorem mrt_liouville_principal_small_height : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ t : ℝ, |t| ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 / 3 : ℝ)) →
        -C ≤ (∑ p ∈ mrtLiouvillePrimeTail X,
          characterTwist (1 : DirichletCharacter ℂ q) t p / (p : ℂ)).re := by
  obtain ⟨c, K, C, hc, hK, hC, hprime⟩ := mrt_prime_cosine_lower
  refine ⟨C + 1, by positivity, ?_⟩
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (mrt_small_height_phase_error c K hc hK),
    hlog.eventually (eventually_ge_atTop (1 : ℝ))] with X herr hL
  intro q hq hqX t ht
  have hL0 : 0 < Real.log (X : ℝ) := by linarith
  have hX0 : (0 : ℝ) < X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL0)
  let a := Real.exp ((Real.log (X : ℝ)) ^ (3 / 4 : ℝ))
  have ha : Real.exp 1 ≤ a := Real.exp_le_exp.mpr (Real.one_le_rpow hL (by norm_num))
  have haX : a ≤ X := by
    rw [← Real.exp_log hX0]
    exact Real.exp_le_exp.mpr (Real.rpow_le_self_of_one_le hL (by norm_num))
  have hp := hprime a X t ha haX
  have he := herr t ht
  have hroot : Real.sqrt ((Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) =
      (Real.log (X : ℝ)) ^ (3 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
    norm_num
  simp only [a, Real.log_exp, hroot] at hp
  have hid : (∑ p ∈ mrtLiouvillePrimeTail X,
      characterTwist (1 : DirichletCharacter ℂ q) t p / (p : ℂ)).re =
      ∑ p ∈ mrtLiouvillePrimeTail X, Real.cos (t * Real.log (p : ℝ)) / p := by
    simp only [Complex.re_sum]
    apply sum_congr rfl
    intro p hp
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, Complex.div_ofReal_re]
    rw [mrt_principal_twist_re hq (mrtPrimeBand_prime hp)
      (mrt_liouville_tail_above_modulus hL hqX hp) t]
  rw [hid]
  change -C - _ ≤ ∑ p ∈ mrtLiouvillePrimeTail X, _ at hp
  linarith

/-- All characters, still restricted to the explicitly proved low-height range. -/
theorem mrt_liouville_all_characters_small_height : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
        |t| ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 / 3 : ℝ)) →
        -C ≤ (∑ p ∈ mrtLiouvillePrimeTail X, characterTwist χ t p / (p : ℂ)).re := by
  obtain ⟨C₁, hC₁, hnon⟩ := mrt_liouville_nonprincipal_small_height
  obtain ⟨C₂, hC₂, hprincipal⟩ := mrt_liouville_principal_small_height
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  filter_upwards [hnon, hprincipal] with X hn hp
  intro q hq hqX χ t ht
  by_cases hχ : χ = 1
  · rw [hχ]
    exact le_trans (by linarith) (hp q hq hqX t ht)
  · have hh := (abs_le.mp (hn q hq hqX χ hχ t ht)).1
    linarith

/-- The Liouville distance bound on the same proved low-height range. -/
theorem mrt_liouville_distance_small_height : ∃ K : ℝ, 0 ≤ K ∧
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
        |t| ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 / 3 : ℝ)) →
        (1 / 10 : ℝ) * Real.log (Real.log (X : ℝ)) - K ≤
          squaredDistance liouville (characterTwist χ t) X := by
  obtain ⟨C, hC, htail⟩ := mrt_liouville_all_characters_small_height
  obtain ⟨D, hD, hmass⟩ := mrt_liouville_prime_tail_mass
  refine ⟨C + D, by positivity, ?_⟩
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htail, hlog.eventually (eventually_ge_atTop (1 : ℝ))] with X ht hL
  intro q hq hqX χ t htx
  have hb := mrt_liouville_distance_band_lower χ t X
    (Real.exp ((Real.log (X : ℝ)) ^ (3 / 4 : ℝ)))
  change (∑ p ∈ mrtLiouvillePrimeTail X, 1 / (p : ℝ)) +
    (∑ p ∈ mrtLiouvillePrimeTail X, characterTwist χ t p / (p : ℂ)).re ≤ _ at hb
  have hh := hmass X hL
  have he := ht q hq hqX χ t htx
  have hLL := Real.log_nonneg hL
  linarith

end TwoPointCorrelations

end OAI
