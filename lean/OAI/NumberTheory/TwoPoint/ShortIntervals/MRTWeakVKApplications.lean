import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKScale
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalSmallHeight
import OAI.NumberTheory.TwoPoint.Halasz.HalaszHighPrimePhases

namespace OAI

/-! Actual character tails and the two required distance consequences of
weak Hurwitz growth. The growth proposition remains an explicit premise. -/

namespace TwoPointCorrelations

open Filter Finset
open scoped Classical

theorem MRTWeakHurwitzGrowthInput.power_prime_tail (h : MRTWeakHurwitzGrowthInput)
    {a : ℝ} (ha : (2 / 3 : ℝ) < a) (ha1 : a ≤ 1) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ᶠ X : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
        ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), T ≤ |t| → |t| ≤ 6 * X →
          |(∑ p ∈ mrtPrimePowerTail a X, characterTwist χ t p / (p : ℂ)).re| ≤ C := by
  obtain ⟨C, T, hC, hT, ht⟩ := h.prime_tail
  refine ⟨C, max T (Real.exp 1), hC, lt_of_lt_of_le hT (le_max_left _ _), ?_⟩
  filter_upwards [mrt_VK_power_tail_parameters ha ha1,
    mrt_prime_power_cutoff_eventually (lt_trans (by norm_num) ha) ha1] with X hp hc
  intro q _ hq χ t hheight htX
  have hTt : T ≤ |t| := (le_max_left _ _).trans hheight
  have hH : 1 ≤ mrtVKLog (2 * t) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < |2 * t| + 3)).mpr
    have hh := (le_max_right T (Real.exp 1)).trans hheight
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  obtain ⟨hw, hb⟩ := hp q hq t htX hH
  rw [mrt_prime_power_tail_cutoff]
  exact ht q χ t _ X hc.1 hc.2 hTt hw hb

/-- This is the full original modulus/height range, conditional only on the
explicit weak Hurwitz growth input. -/
theorem MRTWeakHurwitzGrowthInput.liouville_distance (h : MRTWeakHurwitzGrowthInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ X →
        (1 / 10 : ℝ) * Real.log (Real.log (X : ℝ)) - K ≤
          squaredDistance liouville (characterTwist χ t) X := by
  obtain ⟨C, T, hC, _, ht⟩ := h.power_prime_tail (by norm_num : (2 / 3 : ℝ) < 3 / 4)
    (by norm_num)
  obtain ⟨D, hD, hlo⟩ := mrt_liouville_all_characters_small_height
  apply mrt_liouville_distance_from_prime_tail (C + D)
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := (Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp hlog)).eventually
      (eventually_ge_atTop T)
  filter_upwards [ht, hlo, he] with X ht hlo he
  intro q hq hqX χ t htX
  have hcast (p : ℕ) : ((p : ℝ) : ℂ) = (p : ℂ) := by norm_cast
  simp only [hcast]
  by_cases hs : |t| ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 / 3 : ℝ))
  · have hh := hlo q hq hqX χ t hs
    linarith
  · let : NeZero q := ⟨Nat.ne_of_gt hq⟩
    have hTt : T ≤ |t| := he.trans (le_of_not_ge hs)
    have hXreal : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have h6 : |t| ≤ 6 * (X : ℝ) := htX.trans (by linarith)
    have hh := (abs_le.mp (ht q hqX χ t hTt h6)).1
    change -(C + D) ≤ (∑ p ∈ mrtPrimePowerTail (3 / 4) X,
      characterTwist χ t p / (p : ℂ)).re
    linarith

/-- The three harmonic phases needed for high-prime repulsion use only the
principal character of modulus one. -/
theorem MRTWeakHurwitzGrowthInput.high_prime (h : MRTWeakHurwitzGrowthInput) :
    HalaszHighPrimeInput := by
  obtain ⟨C, T, _, _, ht⟩ := h.power_prime_tail (by norm_num : (2 / 3 : ℝ) < 27 / 40)
    (by norm_num)
  apply halasz_high_prime_of_three_phases
  refine ⟨C, ?_⟩
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := ((tendsto_rpow_atTop (show (0 : ℝ) < 20 by norm_num)).comp hlog).eventually
    (eventually_ge_atTop T)
  filter_upwards [ht, he, hlog.eventually (eventually_ge_atTop (1 : ℝ))] with X ht he hL
  simp only [Function.comp_apply, Real.rpow_ofNat] at he
  intro u hu hux k hk hk3
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3R : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
  have hu0 : 0 ≤ |u| := abs_nonneg u
  have hktu : T ≤ |(k : ℝ) * u| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact he.trans (hu.trans (le_mul_of_one_le_left hu0 hkR))
  have hktX : |(k : ℝ) * u| ≤ 6 * (X : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    have hXreal : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hh := mul_le_mul_of_nonneg_left hux hk0
    have hh' := mul_le_mul_of_nonneg_right hk3R (show (0 : ℝ) ≤ 2 * X by positivity)
    linarith
  have hq : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) :=
    Real.one_le_rpow hL (by norm_num)
  have hh := ht 1 (by simpa using hq) (1 : DirichletCharacter ℂ 1) ((k : ℝ) * u) hktu hktX
  have hid : (∑ p ∈ mrtPrimePowerTail (27 / 40) X,
      characterTwist (1 : DirichletCharacter ℂ 1) ((k : ℝ) * u) p / (p : ℂ)).re =
      ∑ p ∈ mrtPrimePowerTail (27 / 40) X,
        Real.cos ((k : ℝ) * u * Real.log (p : ℝ)) / (p : ℝ) := by
    simp only [Complex.re_sum]
    apply sum_congr rfl
    intro p hp
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, Complex.div_ofReal_re]
    rw [mrt_principal_twist_re (by norm_num) (mrtPrimeBand_prime hp)
      (mrtPrimeBand_prime hp).one_lt]
  rwa [hid] at hh

end TwoPointCorrelations

end OAI
