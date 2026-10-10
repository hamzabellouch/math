import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKPrimeTail
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterSmallHeight

namespace OAI

/-! Quantitative height bookkeeping for the original character range.
Every fixed tail exponent greater than 2/3 absorbs the two logarithmic
factors in the weak VK derivative estimate. -/

namespace TwoPointCorrelations

open Filter
open scoped Classical

lemma mrt_VK_height_upper {X t : ℝ} (hX : 1 ≤ X)
    (hL : Real.log 15 ≤ Real.log X) (ht : |t| ≤ 6 * X) :
    mrtVKLog (2 * t) ≤ 2 * Real.log X := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hh : |2 * t| + 3 ≤ 15 * X := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hl := Real.log_le_log (by positivity : 0 < |2 * t| + 3) hh
  rw [Real.log_mul (by norm_num) hX0.ne'] at hl
  exact hl.trans (by linarith)

lemma mrt_VK_weight_upper {q : ℕ} [NeZero q] {L t : ℝ}
    (hL : 0 < L) (hlogL : 1 ≤ Real.log L)
    (hq : (q : ℝ) ≤ L ^ (1 / 125 : ℝ))
    (hH : mrtVKLog (2 * t) ≤ 2 * L) :
    mrtVKWeight q (2 * t) ≤ 4 * Real.log L := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlogq := Real.log_le_log hq0 hq
  rw [Real.log_rpow hL] at hlogq
  have hlogH := Real.log_le_log (mrt_VKLog_pos (2 * t)) hH
  rw [Real.log_mul (by norm_num) hL.ne'] at hlogH
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  unfold mrtVKWeight
  linarith

lemma mrt_VK_log_square_decay {a : ℝ} (ha : (2 / 3 : ℝ) < a) :
    ∀ᶠ L : ℝ in atTop,
      512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ) ≤ (1 / 2 : ℝ) * L ^ a := by
  let ε := (a - 2 / 3) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hs := (isLittleO_log_rpow_atTop hε).bound (show (0 : ℝ) < 1 / 32 by norm_num)
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with L hs hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL0 _)] at hs
  have hp : (L ^ ε) ^ 2 * L ^ (2 / 3 : ℝ) = L ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    congr 1
    dsimp [ε]
    ring
  calc
    _ ≤ 512 * (((1 / 32 : ℝ) * L ^ ε) ^ 2) * L ^ (2 / 3 : ℝ) := by
      gcongr
      exact Real.log_nonneg hL
    _ = (1 / 2 : ℝ) * ((L ^ ε) ^ 2 * L ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by rw [hp]

/-- Both explicit hypotheses of the finite prime-tail estimate hold in the
original modulus range and at every height up to X. -/
theorem mrt_VK_power_tail_parameters {a : ℝ} (ha : (2 / 3 : ℝ) < a) (_ha1 : a ≤ 1) :
    ∀ᶠ X : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ t : ℝ, |t| ≤ 6 * X → 1 ≤ mrtVKLog (2 * t) →
        (1 / Real.log (mrtPrimePowerCutoff a X : ℝ) ≤ mrtVKRadius (2 * t) / 16) ∧
        ((mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤
          Real.log (mrtPrimePowerCutoff a X : ℝ)) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloga : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 2 / 3) ha
  filter_upwards [hlog.eventually (mrt_VK_log_square_decay ha),
    hlog.eventually (eventually_ge_atTop (max (Real.exp 1) (Real.log 15))),
    mrt_prime_power_cutoff_log_lower hloga,
    eventually_ge_atTop (1 : ℕ)] with X hdecay hL hcut hX
  intro q _ hq t ht hH
  let L := Real.log (X : ℝ)
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlogL : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hLe
    simpa using hh
  have hHupper := mrt_VK_height_upper (by exact_mod_cast hX)
    ((le_max_right _ _).trans hL) ht
  have hW := mrt_VK_weight_upper hL0 hlogL hq hHupper
  have hW0 : 0 ≤ mrtVKWeight q (2 * t) := zero_le_one.trans (mrt_VKWeight_ge_one hH)
  have hW2 := pow_le_pow_left₀ hW0 hW 2
  have hHp : (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ 2 * L ^ (2 / 3 : ℝ) := by
    calc
      _ ≤ (2 * L) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (mrt_VKLog_pos _).le hHupper (by norm_num)
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := Real.mul_rpow (by norm_num) hL0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (Real.rpow_nonneg hL0.le _)
  have hprod := mul_le_mul hW2 hHp (Real.rpow_nonneg (mrt_VKLog_pos _).le _) (sq_nonneg _)
  have hcost : 16 * ((mrtVKWeight q (2 * t)) ^ 2 *
      (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) ≤ Real.log (mrtPrimePowerCutoff a X : ℝ) := by
    have hfirst : 16 * ((mrtVKWeight q (2 * t)) ^ 2 *
        (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) ≤ 512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ) := by
      nlinarith only [hprod]
    exact hfirst.trans (hdecay.trans hcut)
  have hW1 : 1 ≤ (mrtVKWeight q (2 * t)) ^ 2 := by
    nlinarith [mrt_VKWeight_ge_one (q := q) hH]
  have hHp0 : 0 < (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (mrt_VKLog_pos _) _
  have hmass : 16 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤
      Real.log (mrtPrimePowerCutoff a X : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hW1 hHp0.le
    nlinarith only [hh, hcost]
  constructor
  · have hh := one_div_le_one_div_of_le (by positivity :
        0 < 16 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) hmass
    apply hh.trans_eq
    rw [mrtVKRadius, Real.rpow_neg (mrt_VKLog_pos _).le]
    ring
  · have hn : 0 ≤ (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by positivity
    nlinarith only [hcost, hn]

end TwoPointCorrelations

end OAI
