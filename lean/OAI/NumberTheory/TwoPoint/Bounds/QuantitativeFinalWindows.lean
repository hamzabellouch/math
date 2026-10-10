import OAI.NumberTheory.TwoPoint.Walks.CanonicalCenteringBins

namespace OAI

/-! The final logarithmic bins meet both the analytic and spectral
long-window hypotheses, uniformly in the absolute exponent A. -/

namespace TwoPointCorrelations

open Filter

lemma exp_neg_nat_lt_log_two (J : ℕ) (hJ : 1 ≤ J) :
    Real.exp (-(J : ℝ)) < Real.log 2 := by
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have he : 2 < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  have hi : (Real.exp 1)⁻¹ < (1 / 2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    linarith
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  calc
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    _ < (1 / 2 : ℝ) := by simpa only [Real.exp_neg] using hi
    _ ≤ _ := hl

lemma floor_exp_half_bound (Y T : ℝ) (hY : 2 ≤ Y) (hT : Real.exp Y ≤ T) :
    Real.exp (Y / 2) ≤ (⌊T⌋₊ : ℝ) := by
  let E := Real.exp (Y / 2)
  have hE : 2 ≤ E := by
    have he := Real.add_one_le_exp (Y / 2)
    dsimp only [E]
    linarith
  have hsq : E * E ≤ T := by
    calc
      _ = Real.exp Y := by
        dsimp only [E]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ T := hT
  have hf := Nat.lt_floor_add_one T
  change E ≤ _
  nlinarith

lemma final_bin_windows (L X η : ℝ) (A : ℕ) (hL : 2 ≤ L)
    (hA : 1000 ≤ A) (hX : Real.exp (L ^ A) ≤ X) (hη : 0 < η)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    Real.exp (L ^ (1000 : ℝ)) ≤ X ∧
      Real.exp (L ^ A / 2) ≤ (⌊X * Real.exp ((j : ℝ) * η)⌋₊ : ℝ) := by
  have hLone : 1 ≤ L := by linarith
  have hAp : A ≠ 0 := by omega
  have hpow : L ^ (1000 : ℝ) ≤ L ^ A := by
    rw [Real.rpow_ofNat]
    exact pow_le_pow_right₀ hLone hA
  have hY : 2 ≤ L ^ A := hL.trans (le_self_pow₀ hLone hAp)
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  exact ⟨(Real.exp_le_exp.mpr hpow).trans hX,
    floor_exp_half_bound _ _ hY
      (hX.trans (bin_cutoff_ge L η X hη hXp.le j hj))⟩

theorem eventually_quantitative_final_windows (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ 1 ≤ primeSupplyCount W L ∧
      0 < Real.exp (-(primeSupplyCount W L : ℝ)) ∧
      Real.exp (-(primeSupplyCount W L : ℝ)) < Real.log 2 ∧
      ∀ (A : ℕ), 1000 ≤ A → ∀ (X : ℝ), Real.exp (L ^ A) ≤ X →
        Real.exp (L ^ (1000 : ℝ)) ≤ X ∧
        ∀ j ∈ paddingBinIndices L (Real.exp (-(primeSupplyCount W L : ℝ))),
          Real.exp (L ^ A / 2) ≤
            (⌊X * Real.exp ((j : ℝ) * Real.exp (-(primeSupplyCount W L : ℝ)))⌋₊ : ℝ) := by
  filter_upwards [eventually_primeSupplyCount_pos W hW, eventually_ge_atTop (2 : ℝ)]
    with L hJ hL
  refine ⟨hL, hJ, Real.exp_pos _, exp_neg_nat_lt_log_two _ hJ, ?_⟩
  intro A hA X hX
  have hLone : 1 ≤ L := by linarith
  have hpow : L ^ (1000 : ℝ) ≤ L ^ A := by
    rw [Real.rpow_ofNat]
    exact pow_le_pow_right₀ hLone hA
  refine ⟨(Real.exp_le_exp.mpr hpow).trans hX, ?_⟩
  intro j hj
  exact (final_bin_windows L X _ A hL hA hX (Real.exp_pos _) j hj).2

lemma final_log_scale_exact (X : ℝ) (A : ℕ) (hX : 1 ≤ X) (hA : A ≠ 0) :
    Real.exp (((Real.log X) ^ (1 / (A : ℝ))) ^ A) = X := by
  have hp : ((Real.log X) ^ (1 / (A : ℝ))) ^ A = Real.log X := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow (Real.log_nonneg hX) hA
  rw [hp, Real.exp_log (zero_lt_one.trans_le hX)]

lemma final_log_scale_tendsto (A : ℕ) (hA : 0 < A) :
    Tendsto (fun X : ℝ => (Real.log X) ^ (1 / (A : ℝ))) atTop atTop := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast hA
  exact (tendsto_rpow_atTop (one_div_pos.mpr hAp)).comp Real.tendsto_log_atTop

end TwoPointCorrelations

end OAI
