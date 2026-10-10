import OAI.NumberTheory.JointDickman.Probability.PublishedResidueChannel

namespace OAI

/-! # Decay of the residue-channel error at polynomial cell scales -/

namespace JointDickman

open Filter
open scoped Topology

noncomputable def residueDecayEnvelope (M C T : ℝ) (B : ℕ) : ℝ :=
  8 * (T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) *
    (M + C * (B : ℝ) ^ (-(77 : ℝ)) + (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ))) +
  12 * (2 * C * (B : ℝ) ^ (-(74 : ℝ)) + C ^ 2 * (B : ℝ) ^ (-(154 : ℝ)) +
    (9 / 8 : ℝ) * (B : ℝ) ^ (-(994 : ℝ)))

theorem primeComparisonError_power {B : ℕ} (hB : 0 < B) :
    9 / (8 * (auxiliaryCutoff B : ℝ)) = (9 / 8 : ℝ) * (B : ℝ) ^ (-(1000 : ℝ)) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  rw [Real.rpow_neg hB0.le]
  norm_num [auxiliaryCutoff, Real.rpow_natCast]
  ring

theorem residueChannelError_at_min (M C T : ℝ) {B : ℕ} (hB : 0 < B) :
    residueChannelError M C T B ((B : ℝ) ^ (-(3 : ℝ))) 3 =
      residueDecayEnvelope M C T B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hdiv (a b : ℝ) : (B : ℝ) ^ a / (B : ℝ) ^ b = (B : ℝ) ^ (a - b) :=
    (Real.rpow_sub hB0 a b).symm
  have hfirst : (C * (B : ℝ) ^ (-(80 : ℝ)) + 9 / (8 * (auxiliaryCutoff B : ℝ))) /
      (B : ℝ) ^ (-(3 : ℝ)) = C * (B : ℝ) ^ (-(77 : ℝ)) +
        (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ)) := by
    rw [primeComparisonError_power hB, add_div, mul_div_assoc, mul_div_assoc, hdiv, hdiv]
    norm_num only [show (-(80 : ℝ)) - -3 = -77 by norm_num,
      show (-(1000 : ℝ)) - -3 = -997 by norm_num]
  have hs : ((B : ℝ) ^ (-(3 : ℝ))) * (B : ℝ) ^ (-(3 : ℝ)) =
      (B : ℝ) ^ (-(6 : ℝ)) := by rw [← Real.rpow_add hB0]; congr 1; norm_num
  have hp : (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 = C ^ 2 * (B : ℝ) ^ (-(160 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hB0.le]
    congr 2
    norm_num
  have hsecond : (2 * (C * (B : ℝ) ^ (-(80 : ℝ))) +
      (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 + 9 / (8 * (auxiliaryCutoff B : ℝ))) /
      ((B : ℝ) ^ (-(3 : ℝ)) * (B : ℝ) ^ (-(3 : ℝ))) =
      2 * C * (B : ℝ) ^ (-(74 : ℝ)) + C ^ 2 * (B : ℝ) ^ (-(154 : ℝ)) +
        (9 / 8 : ℝ) * (B : ℝ) ^ (-(994 : ℝ)) := by
    rw [hs, hp, primeComparisonError_power hB, add_div, add_div, ← mul_assoc]
    simp only [mul_div_assoc, hdiv]
    norm_num only [show (-(80 : ℝ)) - -6 = -74 by norm_num,
      show (-(160 : ℝ)) - -6 = -154 by norm_num,
      show (-(1000 : ℝ)) - -6 = -994 by norm_num]
  unfold residueChannelError residueDecayEnvelope
  rw [hfirst, hsecond]
  ring

theorem residueChannelError_le_envelope {M C T m mass : ℝ} {B : ℕ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hB : 0 < B)
    (hm : (B : ℝ) ^ (-(3 : ℝ)) ≤ m) (hmass0 : 0 ≤ mass) (hmass : mass ≤ 3) :
    residueChannelError M C T B m mass ≤ residueDecayEnvelope M C T B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hm0 : 0 < (B : ℝ) ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hmpos : 0 < m := hm0.trans_le hm
  have hE : 0 ≤ C * (B : ℝ) ^ (-(80 : ℝ)) := by positivity
  have hκ : 0 ≤ 9 / (8 * (auxiliaryCutoff B : ℝ)) := by positivity
  have h1 := div_le_div_of_nonneg_left (add_nonneg hE hκ) hm0 hm
  have hnum : 0 ≤ 2 * (C * (B : ℝ) ^ (-(80 : ℝ))) +
      (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 + 9 / (8 * (auxiliaryCutoff B : ℝ)) := by positivity
  have h2 := div_le_div_of_nonneg_left hnum
    (mul_pos hm0 hm0) (mul_self_le_mul_self hm0.le hm)
  have hR : 0 ≤ 1 / auxiliaryRatio B := one_div_nonneg.mpr
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B)))
  have hbase : 0 ≤ (B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B :=
    add_nonneg (Real.rpow_nonneg hB0.le _) hR
  have htail : 0 ≤ 8 * (T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) +
      1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) :=
    mul_nonneg (by norm_num) (mul_nonneg hT (Real.rpow_nonneg hbase _))
  rw [← residueChannelError_at_min M C T hB]
  unfold residueChannelError
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h1) htail
  · exact mul_le_mul
      (mul_le_mul_of_nonneg_left h2 (by norm_num)) hmass
      hmass0
      (mul_nonneg (by norm_num) (div_nonneg hnum (mul_nonneg hm0.le hm0.le)))

theorem residueDecayEnvelope_tendsto (M C T : ℝ) :
    Tendsto (residueDecayEnvelope M C T) atTop (𝓝 0) := by
  have hpow (p : ℝ) (hp : 0 < p) :
      Tendsto (fun B : ℕ => (B : ℝ) ^ (-p)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun B => 1 / auxiliaryRatio B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop auxiliaryRatio_tendsto
  have hbase : Tendsto (fun B : ℕ => (B : ℝ) ^ (-(1 / 10 : ℝ)) +
      1 / auxiliaryRatio B) atTop (𝓝 0) := by
    simpa only [add_zero] using (hpow (1 / 10) (by norm_num)).add hinv
  have htail := hbase.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 4)
  have hfirst := ((htail.const_mul T).const_mul 8).mul
    (((hpow 77 (by norm_num)).const_mul C).const_add M |>.add
      ((hpow 997 (by norm_num)).const_mul (9 / 8)))
  have hsecond := ((((hpow 74 (by norm_num)).const_mul (2 * C)).add
      ((hpow 154 (by norm_num)).const_mul (C ^ 2))).add
      ((hpow 994 (by norm_num)).const_mul (9 / 8))).const_mul 12
  convert hfirst.add hsecond using 1
  · funext B
    unfold residueDecayEnvelope
    ring
  · norm_num

end JointDickman

end OAI
