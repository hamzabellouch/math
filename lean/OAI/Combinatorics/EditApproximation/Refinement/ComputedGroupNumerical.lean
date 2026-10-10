import OAI.Combinatorics.EditApproximation.Geometry.GroupNumerical
import OAI.Combinatorics.EditApproximation.Geometry.BandGroupSampling

namespace OAI

/-! Computed parameters discharge the group scale-count and H^-4 tail bounds. -/

namespace EditApproximation

theorem computed_group_scale_count (N eb : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    (groupDyadicScales (integerParameters N).M (2 ^ eb) (inputSmallLog N)).length ≤
      2 * inputSmallLog N := by
  have hlogs := (inputSmallLog_bounds N hN).1
  have hsmall : smallLogExponent N ≤ inputSmallLog N :=
    (smallLogExponent N).lt_two_pow_self.le
  have hdiv := Nat.div_le_div_right (c := 20) hlogs
  change (groupDyadicScales (2 ^ (heightExponent N / 20)) (2 ^ eb)
    ((2 ^ smallLogExponent N : ℕ) : ℚ)).length ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat, groupDyadicScales_length_dyadic]
  omega

theorem computed_height_exp_upper (N : ℕ) (hN : 0 < N) :
    (inputHeight N : ℝ) ≤ Real.exp (inputSmallLog N) := by
  change ((2 ^ heightExponent N : ℕ) : ℝ) ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (heightExponent N)
  rw [← Real.exp_nat_mul, mul_one] at hpower
  have hlogs : (heightExponent N : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast (inputSmallLog_bounds N hN).1
  exact hpower.trans (Real.exp_le_exp.mpr hlogs)

theorem computed_group_member_exp_bound (N : ℕ) (hN : 0 < N)
    (hell : 1764 ≤ inputSmallLog N) :
    (((integerParameters N).P + 1 : ℕ) : ℝ) ^ 2 ≤
      4 * Real.exp (2 * (inputSmallLog N : ℝ) ^ 2) := by
  let ell := inputSmallLog N
  let p := coarseExponent ell
  have hp := coarseExponent_shift_square ell hell
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hpell : (p : ℝ) + 20 ≤ ell := by
    change ((p : ℝ) + 21) ^ 2 ≤ ell at hp
    nlinarith only [hp, hp0]
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hP : ((integerParameters N).P : ℝ) ≤ Real.exp ((ell : ℝ) ^ 2) := by
    change ((inputHeight N ^ (p + 20) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_pow]
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (inputHeight N))
      (computed_height_exp_upper N hN) (p + 20)
    rw [← Real.exp_nat_mul] at h
    have hexponent : ((p + 20 : ℕ) : ℝ) * ell ≤ (ell : ℝ) ^ 2 := by
      push_cast
      nlinarith only [hpell, hell0]
    exact h.trans (Real.exp_le_exp.mpr hexponent)
  have hPone : (1 : ℝ) ≤ (integerParameters N).P := by
    have hNat : 1 ≤ (integerParameters N).P :=
      one_le_pow₀ (Nat.one_le_two_pow (n := heightExponent N))
    exact_mod_cast hNat
  have hplus : (((integerParameters N).P + 1 : ℕ) : ℝ) ≤ 2 * Real.exp ((ell : ℝ) ^ 2) := by
    push_cast
    linarith only [hP, hPone]
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg ((integerParameters N).P + 1)) hplus 2
  rw [mul_pow, ← Real.exp_nat_mul] at hsquare
  norm_num only [Nat.cast_ofNat] at hsquare
  exact hsquare

theorem computed_group_union_failure (N eb members : ℕ) (hN : 0 < N)
    (hell : 1764 ≤ inputSmallLog N)
    (hmembers : members ≤ ((integerParameters N).P + 1) ^ 2) :
    let ell := inputSmallLog N
    let T := (groupDyadicScales (integerParameters N).M (2 ^ eb) ell).length
    (members : ℝ) * T *
      (2 * Real.exp (-((ell : ℝ) ^ 80 * (1 / (2 * (ell : ℝ) ^ 21)) ^ 2 /
        (512 * ell + (4 / 3 : ℝ) * (1 / (2 * (ell : ℝ) ^ 21)))))) ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  dsimp only
  let ell := inputSmallLog N
  let T := (groupDyadicScales (integerParameters N).M (2 ^ eb) ell).length
  have hellR : (8 : ℝ) ≤ ell := by exact_mod_cast (show 8 ≤ ell from by omega)
  have hcount : (members : ℝ) ≤ 4 * Real.exp (2 * (ell : ℝ) ^ 2) := by
    have hcast : (members : ℝ) ≤ (((integerParameters N).P + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hmembers
    exact hcast.trans (computed_group_member_exp_bound N hN hell)
  have hscale : (T : ℝ) ≤ 2 * ell := by
    exact_mod_cast computed_group_scale_count N eb hN (by omega)
  have hnum := group_union_failure_numeric hellR
    (by exact_mod_cast Nat.two_pow_pos (heightExponent N) : (0 : ℝ) < inputHeight N)
    (computed_height_exp_upper N hN) (Nat.cast_nonneg members) hcount (Nat.cast_nonneg T) hscale
  have hexponent := group_normalized_exponent (show (1 : ℝ) ≤ ell from by linarith only [hellR])
  have hexp : Real.exp (-((ell : ℝ) ^ 80 * (1 / (2 * (ell : ℝ) ^ 21)) ^ 2 /
      (512 * ell + (4 / 3 : ℝ) * (1 / (2 * (ell : ℝ) ^ 21))))) ≤
      Real.exp (-((ell : ℝ) ^ 37 / 3000)) :=
    Real.exp_le_exp.mpr (neg_le_neg hexponent)
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2))
    (mul_nonneg (Nat.cast_nonneg members) (Nat.cast_nonneg T))).trans hnum

end EditApproximation

end OAI
