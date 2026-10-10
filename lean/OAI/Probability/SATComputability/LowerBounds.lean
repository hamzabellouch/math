import OAI.Probability.RandomSAT.Main

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology

instance decidableClauseSatisfaction {n k : ℕ} (σ : Assignment n)
    (C : ProperClause n k) : Decidable (SatisfiesClause σ C) := by
  unfold SatisfiesClause
  infer_instance

instance decidableFormulaSatisfaction {n k m : ℕ} (σ : Assignment n)
    (F : Formula n k m) : Decidable (Satisfies σ F) := by
  unfold Satisfies
  infer_instance

instance decidableSatisfiability {n k m : ℕ} (F : Formula n k m) :
    Decidable (Satisfiable F) := by
  unfold Satisfiable
  infer_instance

def rationalProbability (n k m : ℕ) : ℚ :=
  (Fintype.card {F : Formula n k m // Satisfiable F} : ℚ) /
    (Fintype.card (Formula n k m) : ℚ)

theorem rationalProbability_cast (n k m : ℕ) :
    (rationalProbability n k m : ℝ) = properSATProbability n k m := by
  simp only [rationalProbability, properSATProbability, Rat.cast_div, Rat.cast_natCast,
    ← Nat.card_eq_fintype_card]

def rationalCenter (n k : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (mainCap n k), rationalProbability n k (j + 1)) / n

theorem rationalCenter_cast {n k : ℕ} (hkn : k ≤ n) :
    (rationalCenter n k : ℝ) = center n k := by
  simp only [rationalCenter, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast,
    rationalProbability_cast, center, lifetimeMean_eq_sum hkn]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact properSATProbability_eq_survival n k (j + 1)

theorem center_lower_certificate (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ s ≥ N, 0 < s →
      center s k - 4 * (1 + balanceConstant (delta k)) * (s : ℝ)^(-delta k) ≤
        limitingCenter k := by
  obtain ⟨N, hadd, hnext⟩ := center_comparisons k hk
  refine ⟨N, ?_⟩
  intro s hs hpos
  apply ge_of_tendsto (center_tendsto k hk)
  filter_upwards [eventually_ge_atTop (s * s)] with n hn
  apply balanced_tail_bound (fun n => center n k) (by norm_num : (0 : ℝ) ≤ 4)
    (delta_pos hk) hs hpos ?_ ?_ n hn
  · intro r hr t ht
    simpa only [densityWindow, Nat.cast_min] using hadd r hr t ht
  · simpa only [densityWindow] using hnext s hs

theorem rational_lower_certificates :
    ∃ C N : ℕ, 0 < C ∧ 3 ≤ N ∧
      ∀ s : ℕ,
        ((rationalCenter ((N + s + 1)^12) 3 - (C : ℚ) / (s + 1) : ℚ) : ℝ) ≤
          limitingCenter 3 := by
  obtain ⟨N, hN⟩ := center_lower_certificate 3 (by omega)
  obtain ⟨C, hC⟩ := exists_nat_gt (4 * (1 + balanceConstant (delta 3)))
  have hB : 0 < balanceConstant (delta 3) := balanceConstant_pos (delta_pos (by omega))
  refine ⟨C, max N 3, ?_, le_max_right _ _, ?_⟩
  · have : (0 : ℝ) < C := by linarith
    exact_mod_cast this
  · intro s
    let b := max N 3 + s + 1
    have hb : 0 < b := by dsimp [b]; omega
    have hbN : N ≤ b^12 := by
      have hle : b ≤ b^12 := Nat.le_pow (by omega)
      dsimp [b] at *
      omega
    have hb3 : 3 ≤ b^12 := by
      have hle : b ≤ b^12 := Nat.le_pow (by omega)
      dsimp [b] at *
      omega
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hp : ((b^12 : ℕ) : ℝ)^(-delta 3) = (b : ℝ)⁻¹ := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul hbR.le]
      norm_num [delta, Real.rpow_neg_one]
    have hbound := hN (b^12) hbN (pow_pos hb _)
    rw [hp] at hbound
    have hi : (b : ℝ)⁻¹ ≤ ((s : ℝ) + 1)⁻¹ := by
      apply inv_anti₀ (by positivity)
      dsimp [b]
      push_cast
      linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), le_max_left (N : ℝ) 3]
    have hcost : 4 * (1 + balanceConstant (delta 3)) * (b : ℝ)⁻¹ ≤
        (C : ℝ) / (s + 1) := by
      calc
        _ ≤ (C : ℝ) * (b : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hC.le (inv_nonneg.mpr hbR.le)
        _ ≤ (C : ℝ) * ((s : ℝ) + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
        _ = _ := by rw [div_eq_mul_inv]
    change ((rationalCenter (b^12) 3 - (C : ℚ) / (s + 1) : ℚ) : ℝ) ≤ _
    rw [Rat.cast_sub, rationalCenter_cast hb3]
    push_cast
    linarith

theorem rational_lower_certificates_tendsto (C N : ℕ) :
    Tendsto (fun s : ℕ =>
      ((rationalCenter ((N + s + 1)^12) 3 - (C : ℚ) / (s + 1) : ℚ) : ℝ))
      atTop (nhds (limitingCenter 3)) := by
  have hsize : Tendsto (fun s : ℕ => (N + s + 1)^12) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro s
    have hle : N + s + 1 ≤ (N + s + 1)^12 := Nat.le_pow (by omega)
    change s ≤ (N + s + 1)^12
    omega
  have hcenter := (center_tendsto 3 (by omega)).comp hsize
  have hreal : Tendsto (fun s : ℕ => (s : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hcorrection : Tendsto (fun s : ℕ => (C : ℝ) / ((s : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hreal).const_mul (C : ℝ)
  apply (show Tendsto (fun s : ℕ =>
      center ((N + s + 1)^12) 3 - (C : ℝ) / ((s : ℝ) + 1))
      atTop (nhds (limitingCenter 3)) from
        by simpa only [sub_zero, Function.comp_apply] using hcenter.sub hcorrection).congr'
  filter_upwards [hsize.eventually (eventually_ge_atTop 3)] with s hs
  simp only [Rat.cast_sub, rationalCenter_cast hs, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_one]

theorem exists_rational_lower_certificates :
    ∃ C N : ℕ, 0 < C ∧ 3 ≤ N ∧
      (∀ s : ℕ,
        ((rationalCenter ((N + s + 1)^12) 3 - (C : ℚ) / (s + 1) : ℚ) : ℝ) ≤
          limitingCenter 3) ∧
      Tendsto (fun s : ℕ =>
        ((rationalCenter ((N + s + 1)^12) 3 - (C : ℚ) / (s + 1) : ℚ) : ℝ))
        atTop (nhds (limitingCenter 3)) := by
  obtain ⟨C, N, hC, hN, hbound⟩ := rational_lower_certificates
  exact ⟨C, N, hC, hN, hbound, rational_lower_certificates_tendsto C N⟩

end FixedClauseThreshold.Computability

end OAI
