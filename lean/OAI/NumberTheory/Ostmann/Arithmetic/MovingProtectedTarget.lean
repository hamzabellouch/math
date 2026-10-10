import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationGapList

namespace OAI

/-! # The protected target from the actual initial window -/

namespace Ostmann
open Filter

noncomputable def movingProtectedTarget (k : ℕ) (logX G td totalGap : ℝ) : ℝ :=
  (logX - 2 * G - 2 * td + totalGap) / (2 : ℝ) ^ k

/-- A fixed factor in the block width leaves room for every small prime
cell above `exp(exp(.01 L))`. It affects none of the asymptotic estimates. -/
theorem movingProtectedTarget_bounds (k : ℕ) (hk : 2 ≤ k)
    (h G₀ G td totalGap : ℝ) (hh : 0 ≤ h)
    (hGlo : G₀ ≤ G) (hGhi : G ≤ G₀ + 12 * h)
    (herror : |totalGap - 2 * td| ≤ h) :
    16 * h ≤ movingProtectedTarget k (2 * G₀ + 2 ^ (k + 1) * (12 * h)) G td totalGap ∧
      movingProtectedTarget k (2 * G₀ + 2 ^ (k + 1) * (12 * h)) G td totalGap ≤ 32 * h := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hp4 : (4 : ℝ) ≤ 2 ^ k := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at h
    exact h
  have hph := mul_le_mul_of_nonneg_right hp4 hh
  obtain ⟨herrlo, herrhi⟩ := abs_le.mp herror
  unfold movingProtectedTarget
  rw [le_div_iff₀ hp, div_le_iff₀ hp, pow_succ]
  constructor <;> nlinarith only [hGlo, hGhi, herrlo, herrhi, hph, hh]

theorem eventual_protected_target_error (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ totalGap td : ℝ,
      0 ≤ totalGap → totalGap ≤ C * L →
      0 ≤ td → td ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) →
      |totalGap - 2 * td| ≤ Real.exp ((1 / 100 : ℝ) * L) := by
  filter_upwards [arithmetic_exponent_absorption (1 / 1000) (1 / 100) 0 (2 * C) 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hrate
  intro totalGap td hgap0 hgap htd0 htd
  simp only [pow_one, one_mul, zero_mul, Real.exp_zero] at hrate
  rw [abs_le]
  constructor <;> nlinarith only [hgap0, hgap, htd0, htd, hrate]

theorem eventual_protected_cell_target_range :
    ∀ᶠ L : ℝ in atTop, ∀ J cb : ℝ,
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      0 ≤ cb → cb ≤ J / 4 →
      Real.exp ((1 / 100 : ℝ) * L) ≤ (J - cb) / 6 ∧
      (J - cb) / 6 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp ((5 / 10000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [ht.eventually (eventually_ge_atTop (8 : ℝ))] with L hratio
  intro J cb hJlo hJhi hcb0 hcb
  have hs := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg ((1 / 100 : ℝ) * L))
  have heq : Real.exp ((5 / 10000 : ℝ) * L) * Real.exp ((1 / 100 : ℝ) * L) =
      Real.exp ((105 / 10000 : ℝ) * L) := by rw [← Real.exp_add]; congr 1; ring
  rw [heq] at hs
  constructor <;> nlinarith only [hJlo, hJhi, hcb0, hcb, hs,
    Real.exp_nonneg ((1 / 100 : ℝ) * L)]

end Ostmann

end OAI
