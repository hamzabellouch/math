import OAI.NumberTheory.Ostmann.Construction.SelectedSmallPrimes

namespace OAI

/-! # Concrete integer choices for the original moment parameters -/

namespace Ostmann

noncomputable def originalMomentOrder (L V : ℝ) : ℕ := 2 * ⌈L / (2 * V)⌉₊ + 10
noncomputable def originalHolderOrder (V : ℝ) : ℕ := ⌊V ^ (1 / 1000000 : ℝ)⌋₊
noncomputable def originalFrequencyCutoff (V : ℝ) : ℕ := ⌈Real.exp (27 * V / 2)⌉₊

theorem originalMomentOrder_even (L V : ℝ) : Even (originalMomentOrder L V) := by
  refine ⟨⌈L / (2 * V)⌉₊ + 5, ?_⟩
  dsimp [originalMomentOrder]
  omega

theorem originalMomentOrder_scale (L V : ℝ) (hL : 0 ≤ L) (hV : 0 < V) :
    10 ≤ originalMomentOrder L V ∧
      L ≤ ((originalMomentOrder L V - 10 : ℕ) : ℝ) * V ∧
      (originalMomentOrder L V : ℝ) * V ≤ L + 12 * V := by
  let k := ⌈L / (2 * V)⌉₊
  have hceil := Nat.le_ceil (L / (2 * V))
  have hceilU := (Nat.ceil_lt_add_one (div_nonneg hL (by positivity : 0 ≤ 2 * V))).le
  have hlo := (div_le_iff₀ (show 0 < 2 * V by positivity)).mp hceil
  have hhi := (le_div_iff₀ (show 0 < 2 * V by positivity)).mp
    (show (k : ℝ) - 1 ≤ L / (2 * V) by dsimp [k]; linarith)
  have hsub : originalMomentOrder L V - 10 = 2 * k := by dsimp [originalMomentOrder, k]; omega
  refine ⟨by dsimp [originalMomentOrder]; omega, ?_, ?_⟩
  · rw [hsub]
    push_cast
    nlinarith only [hlo]
  · dsimp [originalMomentOrder]
    push_cast
    dsimp [k] at hhi
    nlinarith only [hhi]

theorem originalMomentOrder_size (L V : ℝ) (hV : 0 < V)
    (hlo : V ^ (8 / 5 : ℝ) / 2 ≤ L) (hhi : L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ))
    (hlarge : 60 ≤ V ^ (3 / 5 : ℝ)) :
    V ^ (3 / 5 : ℝ) / 2 ≤ (originalMomentOrder L V : ℝ) ∧
      (originalMomentOrder L V : ℝ) ≤ 2 * V ^ (3 / 5 : ℝ) := by
  have hpow : V ^ (8 / 5 : ℝ) = V * V ^ (3 / 5 : ℝ) := by
    rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, Real.rpow_add hV, Real.rpow_one]
  have hL : 0 ≤ L := (by positivity : 0 ≤ V ^ (8 / 5 : ℝ) / 2).trans hlo
  obtain ⟨hk, hlow, hupp⟩ := originalMomentOrder_scale L V hL hV
  have hsub : ((originalMomentOrder L V - 10 : ℕ) : ℝ) = (originalMomentOrder L V : ℝ) - 10 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hpow] at hlo hhi
  rw [hsub] at hlow
  constructor
  · apply (mul_le_mul_iff_right₀ hV).mp
    nlinarith only [hlow, hlo, hV.le]
  · apply (mul_le_mul_iff_right₀ hV).mp
    nlinarith only [hupp, hhi, mul_nonneg hV.le (sub_nonneg.mpr hlarge)]

theorem originalHolderOrder_bounds (V : ℝ) (hV : 0 ≤ V)
    (hlarge : 2 ≤ V ^ (1 / 1000000 : ℝ)) :
    1 ≤ originalHolderOrder V ∧
      V ^ (1 / 1000000 : ℝ) / 2 ≤ (originalHolderOrder V : ℝ) ∧
      (originalHolderOrder V : ℝ) ≤ V ^ (1 / 1000000 : ℝ) := by
  refine ⟨(Nat.one_le_floor_iff _).mpr (by linarith), ?_, Nat.floor_le (Real.rpow_nonneg hV _)⟩
  have hh := Nat.sub_one_lt_floor (V ^ (1 / 1000000 : ℝ))
  change V ^ (1 / 1000000 : ℝ) - 1 < (originalHolderOrder V : ℝ) at hh
  linarith

end Ostmann

end OAI
