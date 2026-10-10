import OAI.Probability.SATComputability.MaskDelay

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped BigOperators NNReal Topology

theorem poissonKillProbability_le_one {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (r : ℝ≥0) :
    poissonKillProbability U k r ≤ 1 := by
  have h := FiniteLaw.expect_nonneg (candidateBlock r k U) candidateAlive_nonneg
  rw [candidateBlock_expect_alive] at h
  linarith

theorem positive_killing_in_dyadic_bin {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (hU : U.Nonempty)
    (hq : 0 < poissonKillProbability U 2 60) : ∃ j, dyadicBin j U := by
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near_of_lt_one hq
    (poissonKillProbability_le_one U 2 60)
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨j+1, hU, ?_, ?_⟩
  · simpa only [dyadicLevel, inv_pow] using hj.le
  · have he : 2*dyadicLevel (j+1) = ((2 : ℝ)⁻¹)^j := by
      simp only [dyadicLevel, inv_pow, pow_succ]
      norm_num
      ring
    rwa [he]

noncomputable def dyadicLifetimeBound (j : ℕ) : ℝ :=
  (4*(dyadicBlock j : ℝ)/dyadicLevel j)^(1/5 : ℝ)

theorem dyadicLifetimeBound_nonneg (j : ℕ) : 0 ≤ dyadicLifetimeBound j := by
  unfold dyadicLifetimeBound
  positivity [dyadicLevel_pos j]

theorem dyadic_lifetime_bound {n : ℕ} [NeZero n] (r : ℝ≥0)
    (hr : (1 : ℝ)/8 ≤ r) (m j : ℕ) (U : Finset (DeletionCandidate n))
    (hU : dyadicBin j U) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r 3 Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ dyadicLifetimeBound j := by
  have h := maskLifetime_fractional_moment r 3 m (dyadicBlock j) U
    (show 0 < dyadicLevel j/4 by positivity [dyadicLevel_pos j])
    (dyadic_block_kills U j r hr hU.2.1)
  convert h using 1
  unfold dyadicLifetimeBound
  congr 1
  field_simp

theorem capped_lifetime_fractional_bound {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k m M : ℕ) (hm : m ≤ M) (U : Finset (DeletionCandidate n)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r k Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ (M : ℝ)^(1/5 : ℝ) := by
  apply (FiniteLaw.expect_mono _ (g := fun _ => (M : ℝ)^(1/5 : ℝ)) (fun xs => Real.rpow_le_rpow
    (maskLifetime_nonneg U xs) ((maskLifetime_le U xs).trans (by exact_mod_cast hm))
    (by norm_num : (0 : ℝ) ≤ 1/5))).trans_eq
  exact FiniteLaw.expect_const _ _

theorem dyadicLevel_rpow (j : ℕ) : dyadicLevel j = (2 : ℝ)^(-(j : ℝ)) := by
  rw [dyadicLevel, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

theorem dyadicBlock_growth (j : ℕ) :
    (dyadicBlock j : ℝ) ≤ 128*((j : ℝ)+122)^2 * (2 : ℝ)^((j : ℝ)/2) := by
  have he : (((j+1)/2 : ℕ) : ℝ) ≤ (j : ℝ)/2+1 := by
    have h : 2*((j+1)/2) ≤ j+2 := by omega
    have h' : (2 : ℝ)*((j+1)/2 : ℕ) ≤ (j : ℝ)+2 := by exact_mod_cast h
    linarith
  have hp : (2 : ℝ)^((j+1)/2) ≤ 2*(2 : ℝ)^((j : ℝ)/2) := by
    rw [← Real.rpow_natCast]
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num) he).trans_eq
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  unfold dyadicBlock dyadicMultiplicity dyadicTruncation
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 64*((j : ℝ)+122)^2 by positivity)]

noncomputable def dyadicMomentCoefficient (j : ℕ) : ℝ :=
  (dyadicLevel j)^2 * (4*(dyadicBlock j : ℝ)/dyadicLevel j)^(6/5 : ℝ)

theorem dyadicMomentCoefficient_nonneg (j : ℕ) : 0 ≤ dyadicMomentCoefficient j := by
  unfold dyadicMomentCoefficient
  positivity [dyadicLevel_pos j]

theorem dyadicMomentCoefficient_bound (j : ℕ) :
    dyadicMomentCoefficient j ≤
      (512 : ℝ)^(6/5 : ℝ) * ((j : ℝ)+122)^3 * ((2 : ℝ)^(-1/5 : ℝ))^j := by
  have hx : 0 < (j : ℝ)+122 := by positivity
  have hpow : (2 : ℝ)^((j : ℝ)/2) * (2 : ℝ)^(j : ℝ) =
      (2 : ℝ)^(3*(j : ℝ)/2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hA : 4*(dyadicBlock j : ℝ)/dyadicLevel j ≤
      512*((j : ℝ)+122)^2 * (2 : ℝ)^(3*(j : ℝ)/2) := by
    calc
      _ = 4*(dyadicBlock j : ℝ)*(2 : ℝ)^(j : ℝ) := by
        simp only [dyadicLevel, div_eq_mul_inv, inv_inv, Real.rpow_natCast]
      _ ≤ 4*(128*((j : ℝ)+122)^2*(2 : ℝ)^((j : ℝ)/2)) * (2 : ℝ)^(j : ℝ) := by
        gcongr
        exact dyadicBlock_growth j
      _ = _ := by rw [show 4*(128*((j : ℝ)+122)^2*(2 : ℝ)^((j : ℝ)/2)) *
          (2 : ℝ)^(j : ℝ) = 512*((j : ℝ)+122)^2 *
            ((2 : ℝ)^((j : ℝ)/2)*(2 : ℝ)^(j : ℝ)) by ring, hpow]
  have hq : (dyadicLevel j)^2 = (2 : ℝ)^(-2*(j : ℝ)) := by
    rw [dyadicLevel_rpow, pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hxp : (((j : ℝ)+122)^2)^(6/5 : ℝ) = ((j : ℝ)+122)^(12/5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have htwo : ((2 : ℝ)^(3*(j : ℝ)/2))^(6/5 : ℝ) = (2 : ℝ)^(9*(j : ℝ)/5) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have he : (2 : ℝ)^(-2*(j : ℝ)) * (2 : ℝ)^(9*(j : ℝ)/5) =
      ((2 : ℝ)^(-1/5 : ℝ))^j := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  calc
    _ ≤ (dyadicLevel j)^2 *
        (512*((j : ℝ)+122)^2*(2 : ℝ)^(3*(j : ℝ)/2))^(6/5 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity [dyadicLevel_pos j]) hA (by norm_num)) (sq_nonneg _)
    _ = (512 : ℝ)^(6/5 : ℝ) * ((j : ℝ)+122)^(12/5 : ℝ) *
        ((2 : ℝ)^(-1/5 : ℝ))^j := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) (sq_nonneg _), hq, hxp, htwo]
      calc
        _ = (512 : ℝ)^(6/5 : ℝ) * ((j : ℝ)+122)^(12/5 : ℝ) *
          ((2 : ℝ)^(-2*(j : ℝ))*(2 : ℝ)^(9*(j : ℝ)/5)) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := by
      gcongr
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by norm_num)

theorem dyadicMomentCoefficient_summable : Summable dyadicMomentCoefficient := by
  let ρ : ℝ := 2^(-1/5 : ℝ)
  have hρ : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hpoly : Summable (fun j : ℕ => ((j : ℝ)+122)^3*ρ^j) := by
    have h0 := (summable_geometric_of_norm_lt_one hρ).mul_left (122^3 : ℝ)
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hρ).mul_left (3*122^2 : ℝ)
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 2 hρ).mul_left (3*122 : ℝ)
    have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 hρ
    apply (h3.add (h2.add (h1.add h0))).congr
    intro j
    ring
  apply Summable.of_nonneg_of_le dyadicMomentCoefficient_nonneg dyadicMomentCoefficient_bound
  simpa only [mul_assoc, ρ] using hpoly.mul_left ((512 : ℝ)^(6/5 : ℝ))

end FixedClauseThreshold.Computability

end OAI
