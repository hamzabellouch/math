import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterMovingCenter

namespace OAI

/-! The center normalization on shrinking disks costs only the reciprocal
radius. This uses the absolutely convergent Möbius inverse and the proved
residue of the Riemann zeta function; no zero-free hypothesis is used. -/

namespace TwoPointCorrelations

open Complex ArithmeticFunction Filter
open scoped BigOperators Classical Topology LSeries.notation ArithmeticFunction.Moebius

variable {q : ℕ} [NeZero q]

lemma mrt_character_inverse_real_majorant (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤
      ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
  have hm := χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hb : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) := by
    have hh := (LSeriesSummable_one_iff.mpr
      (show 1 < (s.re : ℂ).re by simpa using hs)).norm
    convert hh using 1
    funext n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn, Real.zero_rpow (show s.re ≠ 0 by linarith)]
    · simp [hn]
  have heq := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hne := χ.LSeries_ne_zero_of_one_lt_re hs
  have hi : (LSeries (fun n => χ (n : ZMod q)) s)⁻¹ =
      LSeries (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s := by
    apply mul_left_cancel₀ hne
    simpa only [mul_inv_cancel₀ hne, Pi.mul_def] using heq.symm
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, hi]
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term
        (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hm.norm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
      apply Summable.tsum_le_tsum (fun n => ?_) hm.norm hb
      rw [LSeries.norm_term_eq]
      split_ifs with hn
      · exact div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · exact div_le_div_of_nonneg_right (mrtCharacter_twisted_moebius_norm χ n)
          (Real.rpow_nonneg n.cast_nonneg _)

/-- The local center reciprocal has an absolute radius threshold, independent
of the modulus, character and height. -/
theorem mrt_moving_center_inverse : ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 4 ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
        ‖(DirichletCharacter.LFunction χ (mrtMovingPoint r t 0))⁻¹‖ ≤ 1 / r := by
  have he := tendsto_sub_mul_tsum_nat_rpow.eventually
    (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨ε, hε, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨min (ε / 4) (1 / 4), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro r hr hrr q _ χ t
  have hrε : r ≤ ε / 4 := hrr.trans (min_le_left _ _)
  have hnear : (1 + 2 * r : ℝ) ∈ Metric.ball 1 ε := by
    rw [Metric.mem_ball, Real.dist_eq, show 1 + 2 * r - 1 = 2 * r by ring,
      abs_of_pos (by positivity : 0 < 2 * r)]
    linarith
  have hright : 1 + 2 * r ∈ Set.Ioi (1 : ℝ) := by simp; linarith
  have ht := hlocal ⟨hnear, hright⟩
  have hs : 1 < (mrtMovingPoint r t 0).re := by simp [mrtMovingPoint]; linarith
  have hb := mrt_character_inverse_real_majorant χ hs
  have hre : (mrtMovingPoint r t 0).re = 1 + 2 * r := by simp [mrtMovingPoint]
  rw [hre] at hb
  apply hb.trans
  apply (le_div_iff₀ hr).mpr
  change (1 + 2 * r - 1) * (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * r)) < 2 at ht
  have ht' : 2 * r * (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * r)) < 2 := by
    simpa only [show 1 + 2 * r - 1 = 2 * r by ring] using ht
  nlinarith only [ht']

end TwoPointCorrelations

end OAI
