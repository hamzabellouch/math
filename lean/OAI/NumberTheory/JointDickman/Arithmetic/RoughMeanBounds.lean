import OAI.NumberTheory.JointDickman.Arithmetic.RoughMeanNormalization
import OAI.NumberTheory.JointDickman.Arithmetic.RoughAuxiliaryExpansion

namespace OAI

/-! # Uniform rough coefficient means on the fixed logarithmic scales -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- The normalized summatory mean is bounded uniformly away from the
zero logarithmic scale. Only the cited classical expansion and prime
estimates are used. -/
theorem rough_normalized_mean_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {z δ : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      roughMeanNormalization B z *
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y ≤ C * Y := by
  have hzpos : 0 < z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  obtain ⟨c, hc, _, H, K, hK, hexp⟩ := moving_rough_auxiliary_expansion hSD hM hz 1
  obtain ⟨M, hM0, hprof⟩ := roughMeanProfile_eventually_bounded hM hMP c hc hzpos hzhalf hδ H
  let J : ℝ := (4 : ℝ) ^ z + 1
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hquot : ∀ᶠ B : ℕ in atTop,
      |roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)| ≤ J := by
    have h := (roughMeanNormalization_quotient_tendsto hM hzpos.le (by linarith : z ≤ 1)).abs
    simpa only [abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) z)] using
      h.eventually (eventually_le_nhds (lt_add_one |(4 : ℝ) ^ z|))
  have hlow : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(11 / 100 : ℝ)) ≤ δ :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds hδ)
  refine ⟨K + J * M, by positivity, ?_⟩
  filter_upwards [hexp, hprof, hquot, hlow, roughMeanNormalization_eventually_le hzpos.le,
    eventually_gt_atTop 1] with B hexpB hprofB hquotB hlowB hnorm hB
  intro Y hY hlog
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hBnat : 0 < B := lt_trans Nat.zero_lt_one hB
  have hY0 : 0 ≤ Y := by linarith
  have hs : δ ≤ Real.log Y / B := (le_div_iff₀ hB0).mpr hlog
  have hs0 : 0 < Real.log Y / B := hδ.trans_le hs
  have hpower : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y := by
    have hmul := mul_le_mul_of_nonneg_left hlowB hB0.le
    have heq : (B : ℝ) * (B : ℝ) ^ (-(11 / 100 : ℝ)) = (B : ℝ) ^ (89 / 100 : ℝ) := by
      calc
        _ = (B : ℝ) ^ (1 : ℝ) * (B : ℝ) ^ (-(11 / 100 : ℝ)) := by rw [Real.rpow_one]
        _ = (B : ℝ) ^ ((1 : ℝ) + -(11 / 100 : ℝ)) := (Real.rpow_add hB0 _ _).symm
        _ = _ := by norm_num
    rw [heq] at hmul
    exact hmul.trans (by simpa [mul_comm] using hlog)
  have herror := hexpB Y hpower hY
  have hQ : primeNormalizer (auxiliaryPrimes B) z ≠ 0 := by
    apply ne_of_gt
    unfold primeNormalizer
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact sub_pos.mpr ((div_lt_one hp0).mpr (by linarith))
  let T := Y * ∑ j ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z j * (Real.log Y) ^ (z - 1 - j)
  have hmodel : roughMeanNormalization B z * T = Y *
      (roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) *
        roughMeanProfile c z H B (Real.log Y / B) := by
    rw [roughMeanProfile_eq c z H B hBnat hs0, mul_div_cancel₀ _ hB0.ne']
    dsimp [T]
    field_simp
  have hmodelBound : |roughMeanNormalization B z * T| ≤ Y * (J * M) := by
    rw [hmodel, abs_mul, abs_mul, abs_of_nonneg hY0]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hquotB (hprofB _ hs) (abs_nonneg _) hJ) hY0
  have herrorBound : |roughMeanNormalization B z *
      (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T)| ≤ K * Y := by
    rw [abs_mul, abs_of_nonneg (roughMeanNormalization_nonneg B z)]
    calc
      _ ≤ roughMeanNormalization B z * (K * Y * (B : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left herror (roughMeanNormalization_nonneg B z)
      _ ≤ (B : ℝ) * (K * Y * (B : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = _ := by rw [Real.rpow_neg_one]; field_simp
  calc
    _ = roughMeanNormalization B z *
        (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T) +
        roughMeanNormalization B z * T := by ring
    _ ≤ |roughMeanNormalization B z *
        (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T)| +
        |roughMeanNormalization B z * T| := add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ K * Y + Y * (J * M) := add_le_add herrorBound hmodelBound
    _ = _ := by ring

end JointDickman

end OAI
