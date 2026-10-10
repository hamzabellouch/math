import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothHorizontalBound

namespace OAI

/-! # A zero-avoiding sequence along which both horizontal integrals vanish -/

namespace Ostmann

open Filter
open scoped Topology

theorem smooth_horizontal_integrals_tendsto (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 2 ≤ X) : ∃ t : ℕ → ℝ,
      (∀ n, 0 < t n) ∧ Tendsto t atTop atTop ∧
      (∀ n, ∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t n) ∧
      Tendsto (fun n => smoothHorizontalIntegral χ X (t n)) atTop (𝓝 0) ∧
      Tendsto (fun n => smoothHorizontalIntegral χ X (-t n)) atTop (𝓝 0) := by
  obtain ⟨D, hD, hheight⟩ := exists_smooth_horizontal_bound χ X hX
  choose t ht ht' hzero hbound using fun n : ℕ =>
    hheight ((n : ℝ) + 3) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have htlim : Tendsto t atTop atTop := tendsto_atTop_mono (fun n => (ht n).le) hbase
  have hpower : Tendsto (fun n : ℕ => ((n : ℝ) + 3 + 1) ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ _ hbase)
  have hdecay : Tendsto (fun n : ℕ => D / ((n : ℝ) + 3 + 1) ^ 5) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpower
  refine ⟨t, fun n => by linarith [ht n, Nat.cast_nonneg (α := ℝ) n], htlim, hzero, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hbound n (t n) (.inl rfl)) hdecay
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hbound n (-t n) (.inr rfl)) hdecay

end Ostmann

end OAI
