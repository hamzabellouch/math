import OAI.NumberTheory.JointDickman.Amplification.RegularWeightCap

namespace OAI

/-! # The manuscript's multiplier scale and negligible diagonal cap -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def amplificationMultiplier (B : ℕ) : ℕ := ⌊(B : ℝ) ^ (8/25 : ℝ)⌋₊

theorem amplificationMultiplier_comparable : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
      (B : ℝ) ^ (8/25 : ℝ) / 2 ≤ amplificationMultiplier B ∧
      (amplificationMultiplier B : ℝ) ≤ (B : ℝ) ^ (8/25 : ℝ) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8/25)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually_ge_atTop 2] with B hB
  change 2 ≤ (B : ℝ) ^ (8/25 : ℝ) at hB
  have hl := Nat.lt_floor_add_one ((B : ℝ) ^ (8/25 : ℝ))
  have hpos : 0 < amplificationMultiplier B := by
    apply Nat.floor_pos.mpr
    linarith
  exact ⟨hpos,by dsimp [amplificationMultiplier]; linarith,
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)⟩

theorem amplificationMultiplier_valid : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
      (amplificationMultiplier B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) := by
  have hlim := ((isLittleO_rpow_exp_pos_mul_atTop (8/25 : ℝ)
    (by norm_num : (0 : ℝ) < 1/10)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  filter_upwards [amplificationMultiplier_comparable,
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB he
  refine ⟨hB.1, hB.2.2.trans ?_⟩
  exact (div_le_one (Real.exp_pos _)).mp he

theorem power_div_amplificationMultiplier {r : ℝ} (hr : r < 8/25) :
    Tendsto (fun B : ℕ => (B : ℝ)^r / amplificationMultiplier B) atTop (nhds 0) := by
  have hp := (power_div_power_tendsto_zero hr).comp tendsto_natCast_atTop_atTop
  have hu : ∀ᶠ B : ℕ in atTop,
      (B : ℝ)^r / amplificationMultiplier B ≤ 2*((B : ℝ)^r / (B : ℝ)^(8/25 : ℝ)) := by
    filter_upwards [amplificationMultiplier_comparable,eventually_gt_atTop 0] with B hB hB0
    have hpow : 0 < (B : ℝ)^(8/25 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hB0) _
    have hT : (0 : ℝ) < amplificationMultiplier B := by exact_mod_cast hB.1
    apply (div_le_iff₀ hT).mpr
    have hnon := Real.rpow_nonneg (Nat.cast_nonneg B) r
    calc
      _ = 2*((B : ℝ)^r / (B : ℝ)^(8/25 : ℝ)) * ((B : ℝ)^(8/25 : ℝ)/2) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hB.2.1 (by positivity)
  apply squeeze_zero' (Eventually.of_forall fun B => div_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) hu
  simpa using hp.const_mul 2

/-- Both regular weights together are bounded by one power strictly below
T's exponent, uniformly in the later tail cutoff. -/
theorem regular_pair_cap_negligible {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ Q : ℕ → ℝ,
      Tendsto (fun B => Q B / amplificationMultiplier B) atTop (nhds 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (a : ℕ) (S : Finset ℕ),
        regularCoefficientWeight B L τ C a * regularResidueWeight B L τ C S ≤ Q B := by
  let ε : ℝ := ((8/25 : ℝ) - 2*weightExponent τ)/4
  have hm := (weight_margins_of_le_samplingTau hτsmall).1
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hr : 2*(weightExponent τ + ε) < 8/25 := by dsimp [ε]; linarith
  refine ⟨fun B => (B : ℝ)^(2*(weightExponent τ+ε)),power_div_amplificationMultiplier hr,?_⟩
  filter_upwards [regular_weights_cap hL hτ hε,eventually_gt_atTop 0] with B hB hB0
  intro C a S
  have hab : regularCoefficientWeight B L τ C a * regularResidueWeight B L τ C S ≤
      (B : ℝ)^(weightExponent τ+ε) * (B : ℝ)^(weightExponent τ+ε) :=
    mul_le_mul ((hB C).2 a) ((hB C).1 S) (regularResidueWeight_nonneg B L τ C S)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB0
  rw [← Real.rpow_add hBpos] at hab
  convert hab using 1
  congr 1
  ring

end JointDickman

end OAI
