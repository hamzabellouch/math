import OAI.Dynamics.ConditionalShuffle.OverlayConditioning

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter Topology
namespace Thorp.Conditional
theorem halfDensity_after_step_rho (d : ℕ) (v : RawState (d + 1))
    (c : Coins (d + 1)) (h : Bool)
    (ρ : ℝ) (hm : ρ * Fintype.card (Position (d + 1)) ≤ freeCount v.free)
    (hc : freeCount v.free ≤ 4 * pairHalfCount (v.free ∘ (splitPosition d).symm) c h) :
    (ρ / 2) ≤ startHalfDensity d (rawNext d v c) h := by
  unfold startHalfDensity
  rw [halfCount_after_step]
  have hn : Fintype.card (Position (d + 1)) = 2 * Fintype.card (Position d) := by
    simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin, pow_succ, Nat.mul_comm]
  rw [hn, Nat.cast_mul, Nat.cast_ofNat] at hm
  have hc' : (freeCount v.free : ℝ) ≤
      4 * (pairHalfCount (v.free ∘ (splitPosition d).symm) c h : ℝ) := by exact_mod_cast hc
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := Position d))).mpr
  nlinarith

theorem expectedNoise_dimension_rho (d : ℕ) (v : CenteredState (d + 2))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hm : ρ * Fintype.card (Position (d + 2)) ≤ freeCount v.free) :
    expectedNoise (d + 1) v (d + 2) ≤ (1 - ρ / 2) * expectedEnergy (d + 1) v (d + 2) +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  let B := v.free ∘ (splitPosition (d + 1)).symm
  let bad (c : Coins (d + 2)) : Prop :=
    4 * pairHalfCount B c false < pairFreeCount B ∨
    4 * pairHalfCount B c true < pairFreeCount B
  have hlocal (c : Coins (d + 2)) :
      expectedNoise (d + 1) (nextState (d + 1) v c) (d + 1) ≤
      (1 - ρ / 2) * expectedEnergy (d + 1) (nextState (d + 1) v c) (d + 1) +
        (if bad c then 1 else 0) := by
    by_cases hc : bad c
    · rw [ite_eq_left hc]
      have hle := expectedNoise_le_energy (d + 1) (nextState (d + 1) v c) (d + 1)
      have hone := expectedEnergy_le_one (d + 1) (nextState (d + 1) v c) (d + 1)
      have hnon := expectedEnergy_nonneg (d + 1) (nextState (d + 1) v c) (d + 1)
      nlinarith
    · rw [ite_eq_right hc, add_zero]
      have hb (h : Bool) : (ρ / 2) ≤
          startHalfDensity (d + 1) (nextState (d + 1) v c).raw h := by
        apply halfDensity_after_step_rho (d + 1) v.raw c h ρ hm
        have hf : ¬ 4 * pairHalfCount B c false < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.1
        have ht : ¬ 4 * pairHalfCount B c true < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.2
        change freeCount v.free ≤ 4 * pairHalfCount B c h
        cases h
        · exact Nat.le_of_not_gt hf
        · exact Nat.le_of_not_gt ht
      convert noise_bound_balanced_state d (nextState (d + 1) v c) (ρ / 2) hb using 1
  have hmean := mean_le_mean hlocal
  rw [mean_add, mean_const_mul, ← expectedNoise_first, ← expectedEnergy_first] at hmean
  have hbad := pair_both_half_balance B
  have hbad' : mean (fun c : Coins (d + 2) => if bad c then (1 : ℝ) else 0) ≤
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
    change mean (fun c : Position (d + 1) → Bool => if bad c then (1 : ℝ) else 0) ≤ _
    simpa only [bad, B, pairFreeCount_physical] using hbad
  exact hmean.trans (add_le_add (le_refl _) hbad')

theorem expectedNoise_bound_rho (d : ℕ) (v : CenteredState (d + 2))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hm : ρ * Fintype.card (Position (d + 2)) ≤ freeCount v.free)
    (s : ℕ) (hs : d + 2 ≤ s) :
    expectedNoise (d + 1) v s ≤ (1 - ρ / 2) * expectedEnergy (d + 1) v s +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm (d + 2) a, expectedNoise_add, expectedEnergy_add]
  have he := mean_le_mean (fun ω : History (d + 2) a =>
    expectedNoise_dimension_rho d (iterateState (d + 1) v a ω) ρ hρ hρ₁
      (by simpa only [iterateState_freeCount] using hm))
  simpa only [iterateState_freeCount, mean_add, mean_const_mul, mean_const] using he

theorem expectedEnergy_decay_rho (d : ℕ) (v : CenteredState (d + 2))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hm : ρ * Fintype.card (Position (d + 2)) ≤ freeCount v.free) (t : ℕ) :
    expectedEnergy (d + 1) v t ≤
      (1 - ρ / 4) ^ t / (1 - ρ / 4) ^ (2 * (d + 2)) +
        (4 / ρ) * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := scalar_decay (d + 2) (expectedEnergy (d + 1) v)
    (expectedNoise (d + 1) v) (ρ / 2) (1 - ρ / 4)
    (2 * (9 / 10 : ℝ) ^ freeCount v.free)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by positivity) (expectedEnergy_le_one (d + 1) v)
    (expectedEnergy_recurrence (d + 1) v)
    (by intro s hs; exact expectedNoise_bound_rho d v ρ hρ hρ₁ hm s hs) t
  convert he using 1 ; ring

def resetS (ρ : ℝ) : ℕ := ⌈320 / ρ⌉₊

lemma resetS_large (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) : 2 ≤ resetS ρ := by
  have hh := Nat.le_ceil (320 / ρ)
  have hdiv : (320 : ℝ) ≤ 320 / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  have : (2 : ℝ) ≤ (resetS ρ : ℝ) := by dsimp [resetS]; linarith
  exact_mod_cast this

lemma reset_gamma_power (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    (1 - ρ / 4) ^ (2 * resetS ρ - 2) ≤ (1/2 : ℝ)^32 := by
  have hs := resetS_large ρ hρ hρ₁
  have hc : (320 : ℝ) ≤ ρ * (resetS ρ : ℝ) := by
    have := (div_le_iff₀ hρ).mp (Nat.le_ceil (320 / ρ))
    dsimp [resetS]; nlinarith
  have hcast : ((2 * resetS ρ - 2 : ℕ) : ℝ) = 2 * (resetS ρ : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
  have hbase : 1 - ρ / 4 ≤ Real.exp (-ρ / 4) := by
    convert Real.add_one_le_exp (-ρ / 4) using 1 ; ring
  have ht : -(ρ / 4) * (2 * (resetS ρ : ℝ) - 2) ≤ -32 := by nlinarith
  have he : Real.exp (-1) ≤ (1/2 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    have := Real.add_one_le_exp (1 : ℝ)
    norm_num at this ⊢
    exact this
  calc
    _ ≤ Real.exp (-ρ / 4) ^ (2 * resetS ρ - 2) :=
      pow_le_pow_left₀ (by linarith) hbase _
    _ = Real.exp (-(ρ / 4) * (2 * (resetS ρ : ℝ) - 2)) := by
      rw [← Real.exp_nat_mul, hcast]; congr 1; ring
    _ ≤ Real.exp (-32) := Real.exp_le_exp.mpr ht
    _ = Real.exp (-1) ^ 32 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he _

lemma reset_energy_bound (d : ℕ) (v : CenteredState (d + 2))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hm : ρ * Fintype.card (Position (d + 2)) ≤ freeCount v.free) :
    expectedEnergy (d + 1) v (2 * resetS ρ * (d + 2)) ≤
      (1/2 : ℝ)^(32*(d+2)) + (4 / ρ) * ((9/10 : ℝ)^ρ)^((2 : ℕ)^(d+2)) := by
  have hγ : 0 < 1 - ρ / 4 := by linarith
  have hs := resetS_large ρ hρ hρ₁
  have he := expectedEnergy_decay_rho d v ρ hρ hρ₁ hm (2 * resetS ρ * (d+2))
  have hp : (1-ρ/4)^(2*resetS ρ*(d+2)) / (1-ρ/4)^(2*(d+2)) =
      ((1-ρ/4)^(2*resetS ρ-2))^(d+2) := by
    rw [← pow_mul]
    have hn : 2*resetS ρ*(d+2) = (2*resetS ρ-2)*(d+2)+2*(d+2) := by
      rw [← Nat.add_mul]; congr 1; omega
    rw [hn, pow_add, mul_div_cancel_right₀ _ (ne_of_gt (pow_pos hγ _))]
  rw [hp] at he
  have hpow := pow_le_pow_left₀ (pow_nonneg hγ.le _) (reset_gamma_power ρ hρ hρ₁) (d+2)
  rw [pow_mul]
  apply he.trans (add_le_add hpow (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  rw [← Real.rpow_natCast (9/10 : ℝ), ← Real.rpow_natCast ((9/10 : ℝ)^ρ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9/10)]
  apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
  simpa only [card_position] using hm

lemma reset_noise_scaled_tendsto (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun D : ℕ => (2^D : ℝ)^20 *
      ((4/ρ) * ((9/10 : ℝ)^ρ)^((2 : ℕ)^D))) atTop (nhds 0) := by
  have ha : 0 ≤ (9/10 : ℝ)^ρ := Real.rpow_nonneg (by norm_num) _
  have ha₁ : (9/10 : ℝ)^ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hρ
  have hh := ((tendsto_pow_const_mul_const_pow_of_lt_one 20 ha ha₁).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))).const_mul (4/ρ)
  simpa only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat, mul_zero,
    mul_left_comm] using hh

lemma reset_energy_eventually (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∀ᶠ d : ℕ in atTop, ∀ v : CenteredState (d+2),
      ρ * Fintype.card (Position (d+2)) ≤ freeCount v.free →
      expectedEnergy (d+1) v (2*resetS ρ*(d+2)) ≤ (1/2 : ℝ)^(20*(d+2)) := by
  obtain ⟨D, hD⟩ := eventually_atTop.mp
    ((tendsto_order.mp (reset_noise_scaled_tendsto ρ hρ)).2 (1/2) (by norm_num))
  filter_upwards [eventually_ge_atTop D] with d hd
  intro v hm
  have hn := (hD (d+2) (by omega)).le
  have hlead : (2^(d+2) : ℝ)^20 * (1/2 : ℝ)^(32*(d+2)) ≤ 1/2 := by
    have he : (2^(d+2) : ℝ)^20 * (1/2 : ℝ)^(32*(d+2)) = (1/2 : ℝ)^(12*(d+2)) := by
      rw [← pow_mul, Nat.mul_comm (d+2) 20, pow_mul, pow_mul, ← mul_pow, pow_mul]
      norm_num
    rw [he]
    simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) (show 1 ≤ 12*(d+2) by omega)
  have he := mul_le_mul_of_nonneg_left (reset_energy_bound d v ρ hρ hρ₁ hm)
    (by positivity : (0 : ℝ) ≤ (2^(d+2) : ℝ)^20)
  have hone : (2^(d+2) : ℝ)^20 * (1/2 : ℝ)^(20*(d+2)) = 1 := by
    rw [← pow_mul, Nat.mul_comm (d+2) 20, pow_mul, pow_mul, ← mul_pow]
    norm_num
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (2^(d+2) : ℝ)^20)).mp
  rw [hone]; nlinarith

end Thorp.Conditional

end

end OAI
