import OAI.NumberTheory.JointDickman.Probability.UniformResidueChannel

namespace OAI

/-! # The quantitative residue-decay rate -/

namespace JointDickman

open Filter
open scoped Topology

theorem auxiliary_inv_ratio_eventually_le :
    ∀ᶠ B : ℕ in atTop, 1 / auxiliaryRatio B ≤ (B : ℝ) ^ (-(1 / 10 : ℝ)) := by
  have ht : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ) ^ (9 / 10 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def, mul_zero] using
      ((log_power_div_power_tendsto_zero 1 (by norm_num : (0 : ℝ) < 9 / 10)).comp
        tendsto_natCast_atTop_atTop).const_mul 1000
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hlim hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hp : (B : ℝ) ^ (9 / 10 : ℝ) = B * (B : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [show (9 / 10 : ℝ) = 1 + -(1 / 10 : ℝ) by norm_num, Real.rpow_add hB0, Real.rpow_one]
  have heq : (1 / auxiliaryRatio B) / (B : ℝ) ^ (-(1 / 10 : ℝ)) =
      1000 * (Real.log B / (B : ℝ) ^ (9 / 10 : ℝ)) := by
    rw [hp]
    simp only [auxiliaryRatio, one_div, inv_div]
    ring
  apply (div_le_one (Real.rpow_pos_of_pos hB0 _)).mp
  rw [heq]
  exact hlim.le

theorem residueDecayEnvelope_power_bound {M C T : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      residueDecayEnvelope M C T B ≤ K * (B : ℝ) ^ (-(1 / 40 : ℝ)) := by
  let K := 8 * T * (2 : ℝ) ^ (1 / 4 : ℝ) * (M + C + 9 / 8) +
    12 * (2 * C + C ^ 2 + 9 / 8)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  filter_upwards [auxiliary_inv_ratio_eventually_le, eventually_ge_atTop 1] with B hR hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hp1 (p : ℝ) (hp : 0 ≤ p) : (B : ℝ) ^ (-p) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB1 (neg_nonpos.mpr hp)
  have hpdec (p : ℝ) (hp : 1 / 40 ≤ p) :
      (B : ℝ) ^ (-p) ≤ (B : ℝ) ^ (-(1 / 40 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB1 (neg_le_neg hp)
  have hR0 : 0 ≤ 1 / auxiliaryRatio B := one_div_nonneg.mpr
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B)))
  have htail : ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (-(1 / 40 : ℝ)) := by
    calc
      _ ≤ (2 * (B : ℝ) ^ (-(1 / 10 : ℝ))) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hB0.le _), ← Real.rpow_mul hB0.le]
        congr 2
        norm_num
  have hsecond : M + C * (B : ℝ) ^ (-(77 : ℝ)) +
      (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ)) ≤ M + C + 9 / 8 := by
    have h77 := mul_le_mul_of_nonneg_left (hp1 77 (by norm_num)) hC
    have h997 := mul_le_mul_of_nonneg_left (hp1 997 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 9 / 8)
    linarith
  have hfirst := mul_le_mul htail hsecond (by positivity : (0 : ℝ) ≤
      M + C * (B : ℝ) ^ (-(77 : ℝ)) + (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ))) (by positivity)
  have h74 := mul_le_mul_of_nonneg_left (hpdec 74 (by norm_num)) (by positivity : 0 ≤ 2 * C)
  have h154 := mul_le_mul_of_nonneg_left (hpdec 154 (by norm_num)) (sq_nonneg C)
  have h994 := mul_le_mul_of_nonneg_left (hpdec 994 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 9 / 8)
  unfold residueDecayEnvelope
  have hscaled := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 8 * T)
  dsimp [K]
  nlinarith

open Classical in
/-- The squared residue norm has the stronger rate B^(-1/40), so taking
square roots also gives the manuscript's weaker B^(-1/200) norm rate. -/
theorem manuscriptChannel_residue_rate
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ m₁ : ℕ, 0 < m₁ → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
        (channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) *
          (manuscriptChannel m₁ B q f a -
            finiteResidueAverage (fun r => manuscriptChannel m₁ B q f (a.1, r))) ^ 2) ≤
        (K * (B : ℝ) ^ (-(1 / 40 : ℝ))) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨M, C, T, hM0, hC, hT, hbound⟩ := manuscriptChannel_residue_envelope hSD hSW hM hMP
  obtain ⟨K, hK, hrate⟩ := residueDecayEnvelope_power_bound hM0 hC.le hT.le
  refine ⟨K, hK, ?_⟩
  intro m₁ hm₁
  filter_upwards [hbound m₁ hm₁, hrate] with B hboundB hrateB
  intro q _ hq f
  exact (hboundB q hq f).trans (mul_le_mul_of_nonneg_right hrateB
    (Finset.sum_nonneg (fun x _ => mul_nonneg
      (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))))

end JointDickman

end OAI
