import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWeylBound

namespace OAI

/-! # An effective inverse conclusion for a large quadratic sum

All assumptions below are explicit numerical scale inequalities. The rational
approximation and exponential-sum bound are proved, not supplied as inputs.
-/

namespace Ostmann

open scoped BigOperators

private theorem weyl_numeric_contradiction (N Q r B ρ V : ℝ)
    (hN : 0 < N) (hr : 0 < r) (hB : 1 ≤ B) (hρ : 0 < ρ)
    (hrQ : r ≤ Q) (hsmallN : 512 * B ≤ ρ * N)
    (hsmallQ : 512 * Q * B ≤ ρ * N ^ 2)
    (hrlarge : 512 ≤ ρ * r)
    (hlower : ρ * N ^ 2 ≤ V)
    (hupper : V ≤ 64 * (N / r + 1) * (N + r * B)) : False := by
  let T := ρ * N ^ 2 / 512
  have hT : 0 < T := by dsimp [T]; positivity
  have hfirst : N ^ 2 / r ≤ T := by
    apply (div_le_iff₀ hr).mpr
    dsimp [T]
    nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hrlarge)]
  have hsecond : N * B ≤ T := by
    dsimp [T]
    nlinarith [mul_le_mul_of_nonneg_left hsmallN hN.le]
  have hthird : N ≤ T := by
    have hh := mul_le_mul_of_nonneg_left hB hN.le
    linarith
  have hfourth : r * B ≤ T := by
    have hh := mul_le_mul_of_nonneg_right hrQ (show 0 ≤ B by linarith)
    dsimp [T]
    linarith
  have heq : 64 * (N / r + 1) * (N + r * B) =
      64 * (N ^ 2 / r + N * B + N + r * B) := by
    field_simp
    ring
  rw [heq] at hupper
  dsimp [T] at hfirst hsecond hthird hfourth hT
  nlinarith

/-- A large sum forces a denominator O(1/ρ), with approximation precision
1/(Q+1). The stated scale conditions are precisely those used to choose Q. -/
theorem quadratic_inverse_approximation (α β ρ B : ℝ) (N Q : ℕ)
    (hN : 0 < N) (hQ : 0 < Q) (hρ : 0 < ρ) (hB : 1 ≤ B)
    (hlog : 1 + Real.log (Q : ℝ) ≤ B)
    (hsmallN : 512 * B ≤ ρ * N)
    (hsmallQ : 512 * (Q : ℝ) * B ≤ ρ * (N : ℝ) ^ 2)
    (hlarge : ρ * (N : ℝ) ^ 2 ≤
      ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1024 / ρ ∧
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℤ)| ≤ 1 / ((Q : ℝ) + 1) := by
  obtain ⟨a, r, hr, hrQ, hcop, happ, happ'⟩ := exists_reduced_phase_approximation (2 * α) Q hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ1 : ρ ≤ 1 := by
    have hnorm : ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range N, ‖realQuadraticPhase α β j‖ := norm_sum_le _ _
        _ = N := by simp [realQuadraticPhase]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_pos_of_pos hNpos]
  have hrsmall : (r : ℝ) ≤ 512 / ρ := by
    by_contra hh
    have hrlarge : 512 ≤ ρ * (r : ℝ) := by
      have hh' : 512 / ρ < (r : ℝ) := lt_of_not_ge hh
      nlinarith [(div_lt_iff₀ hρ).mp hh']
    have hr2 : 2 ≤ r := by
      by_contra hlt
      have hre : r = 1 := by omega
      have hR : (1 : ℝ) < r := by
        nlinarith
      exact (lt_irrefl (1 : ℝ)) (by simpa only [hre, Nat.cast_one] using hR)
    have hw := quadratic_weyl_bound α β a r N hr2 hcop happ'
    have hrQR : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
    have hlogr : 1 + Real.log (r : ℝ) ≤ B := by
      have hh := Real.log_le_log hrR hrQR
      linarith
    have hw' : ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
        64 * ((N : ℝ) / r + 1) * ((N : ℝ) + r * B) := by
      apply hw.trans
      gcongr
    exact weyl_numeric_contradiction N Q r B ρ _ hNpos hrR hB hρ
      (by exact_mod_cast hrQ) hsmallN hsmallQ hrlarge hlarge hw'
  refine ⟨2 * r, by omega, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hrsmall (by norm_num : (0 : ℝ) ≤ 2)
    push_cast
    exact hh.trans_eq (by ring)
  · have hround := round_le (((2 * r : ℕ) : ℝ) * α) a
    apply hround.trans
    have hh := mul_le_mul_of_nonneg_left happ hrR.le
    have hid : (r : ℝ) * |2 * α - (a : ℝ) / r| = |((2 * r : ℕ) : ℝ) * α - a| := by
      calc
        _ = |(r : ℝ) * (2 * α - (a : ℝ) / r)| := by rw [abs_mul, abs_of_pos hrR]
        _ = _ := by
          congr 1
          push_cast
          field_simp
    rw [hid] at hh
    convert hh using 1
    field_simp

end Ostmann

end OAI
