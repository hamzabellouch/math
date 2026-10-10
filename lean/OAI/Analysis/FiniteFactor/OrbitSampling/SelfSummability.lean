import OAI.Analysis.FiniteFactor.OrbitSampling.ProductMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingSelfBudget (stage : ℕ) : ℝ :=
  (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ))^(sourceSamplingPrefix stage).card /
    ((sourceSamplingPowers stage).card : ℝ)

/-- A concrete logarithmic estimate sufficient for the source exponent gap. -/
theorem sampling_self_base_bound (m : ℝ) (hm1 : 1 ≤ m) (hlarge : 802 ≤ m^(1/50 : ℝ)) :
    2+8*m^(3/5 : ℝ)*Real.log m ≤ m^(63/100 : ℝ) := by
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hl := Real.log_le_rpow_div hm.le (by norm_num : (0 : ℝ) < 1/100)
  have he : m^(3/5 : ℝ)*m^(1/100 : ℝ) = m^(61/100 : ℝ) := by
    rw [← Real.rpow_add hm]; norm_num
  have hpow : 1 ≤ m^(61/100 : ℝ) := Real.one_le_rpow hm1 (by norm_num)
  have hmul : m^(3/5 : ℝ)*Real.log m ≤ 100*m^(61/100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hm.le (3/5 : ℝ))
    rw [← mul_div_assoc,he] at hh
    linarith
  calc
    _ ≤ 802*m^(61/100 : ℝ) := by linarith
    _ ≤ m^(1/50 : ℝ)*m^(61/100 : ℝ) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = _ := by rw [← Real.rpow_add hm]; norm_num

theorem sourceSamplingSelfBudget_eventually : ∀ᶠ stage in atTop,
    sourceSamplingSelfBudget stage ≤ (sourceBlockSize stage : ℝ)^(-(1/25 : ℝ)*(sourceBlockSize stage : ℝ)) := by
  have ht : Tendsto (fun stage => (sourceBlockSize stage : ℝ)^(1/50 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/50)).comp
      (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  filter_upwards [ht.eventually (eventually_ge_atTop 802),sourceSamplingPowers_eventually] with stage hlarge hspec
  let m : ℝ := sourceBlockSize stage
  let B := 2+8*m^(3/5 : ℝ)*Real.log m
  let P : ℝ := (sourceSamplingPowers stage).card
  have hm : 0 < m := sourceBlockSize_pos stage
  have hm1 : 1 ≤ m := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    dsimp [m]; linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity [Real.log_nonneg hm1]
  have hB : B ≤ m^(63/100 : ℝ) := sampling_self_base_bound m hm1 hlarge
  have hnum : B^(sourceSamplingPrefix stage).card ≤ m^((65/100 : ℝ)*m) := by
    calc
      _ ≤ (m^(63/100 : ℝ))^(sourceSamplingPrefix stage).card := pow_le_pow_left₀ hB0 hB _
      _ = m^((63/100 : ℝ)*((sourceSamplingPrefix stage).card : ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hm.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 (by
        have hd := sourceSamplingPrefix_card_bound stage
        change ((sourceSamplingPrefix stage).card : ℝ) ≤ (101/100 : ℝ)*m at hd
        nlinarith)
  have hP : m^((69/100 : ℝ)*m) ≤ P := hspec.2.1
  have hPpos : 0 < P := (Real.rpow_pos_of_pos hm _).trans_le hP
  change B^(sourceSamplingPrefix stage).card/P ≤ m^(-(1/25 : ℝ)*m)
  calc
    _ ≤ m^((65/100 : ℝ)*m)/P := div_le_div_of_nonneg_right hnum hPpos.le
    _ ≤ m^((65/100 : ℝ)*m)/m^((69/100 : ℝ)*m) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hP
    _ = _ := by rw [← Real.rpow_sub hm]; congr 1; ring

/-- The actual block growth makes the inverse-square stage sequence summable. -/
theorem sourceSampling_inverse_square_summable : Summable (fun stage => (sourceBlockSize stage : ℝ)^(-2 : ℝ)) := by
  have hg : Summable (fun stage : ℕ => (1/4 : ℝ)^stage) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply hg.of_nonneg_of_le (fun _ => by positivity)
  intro stage
  have hp : (2 : ℝ)^stage ≤ sourceBlockSize stage := by
    have hh := (sourceStage stage).m_ge_pow
    have hle : 2^stage ≤ 2^(stage+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hle.trans hh
  calc
    _ ≤ ((2 : ℝ)^stage)^(-2 : ℝ) := Real.rpow_le_rpow_of_nonpos (by positivity) hp (by norm_num)
    _ = _ := by
      rw [Real.rpow_neg (by positivity),Real.rpow_two]
      rw [← pow_mul, Nat.mul_comm stage 2, pow_mul, ← inv_pow]
      norm_num

/-- Summability of the actual full-product self-pair budget. -/
theorem sourceSamplingSelfBudget_summable : Summable sourceSamplingSelfBudget := by
  apply sourceSampling_inverse_square_summable.of_norm_bounded_eventually_nat
  filter_upwards [sourceSamplingSelfBudget_eventually] with stage hb
  have hm : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
  have hn : 0 ≤ sourceSamplingSelfBudget stage := by
    unfold sourceSamplingSelfBudget
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ sourceBlockSize stage by linarith)
    positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact hb.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith))

end
end FiniteFactor

end OAI
