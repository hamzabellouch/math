import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.PrimeShellIndex

namespace OAI

/-! # The top prime controls every nonempty bulk-word bin -/

namespace Ostmann

open Filter
open scoped BigOperators

noncomputable def wordLogBin {m : ℕ} (τ : ℝ) (ℓ : Fin (m + 1) → ℝ) :
    Fin (⌊4 * τ⌋₊ + 1) :=
  ⟨min ⌊∑ i, ℓ i⌋₊ ⌊4 * τ⌋₊, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem wordLogBin_val {m : ℕ} (τ : ℝ) (ℓ : Fin (m + 1) → ℝ)
    (h : (∑ i, ℓ i) ≤ 4 * τ) :
    (wordLogBin τ ℓ).val = ⌊∑ i, ℓ i⌋₊ := by
  exact Nat.min_eq_left (Nat.floor_mono h)

theorem wordLogBin_count (τ : ℝ) (hτ : 1 ≤ τ) :
    Real.log (Fintype.card (Fin (⌊4 * τ⌋₊ + 1))) ≤ Real.log 5 + Real.log τ := by
  have hτpos : 0 < τ := by linarith
  have hfloor := Nat.floor_le (show 0 ≤ 4 * τ by positivity)
  have hcount : ((⌊4 * τ⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * τ := by
    push_cast
    linarith
  have hc : (0 : ℝ) < (⌊4 * τ⌋₊ + 1 : ℕ) := by positivity
  simpa only [Fintype.card_fin, Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hτpos.ne']
    using Real.log_le_log hc hcount

theorem top_word_bin_bounds (m : ℕ) (ℓ : Fin (m + 1) → ℝ) (b τ : ℝ)
    (hτ : 2 ≤ τ) (hbulk : ∀ i : Fin m, 0 ≤ ℓ i.castSucc ∧ ℓ i.castSucc ≤ b)
    (hsize : (m : ℝ) * b ≤ τ)
    (htop : τ ≤ ℓ (Fin.last m) ∧ ℓ (Fin.last m) ≤ 3 * τ) :
    τ / 2 ≤ (⌊∑ i, ℓ i⌋₊ : ℝ) ∧ (⌊∑ i, ℓ i⌋₊ : ℝ) ≤ 4 * τ := by
  have hb0 : 0 ≤ ∑ i : Fin m, ℓ i.castSucc :=
    Finset.sum_nonneg (fun i _ => (hbulk i).1)
  have hb1 : (∑ i : Fin m, ℓ i.castSucc) ≤ (m : ℝ) * b := by
    calc
      _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum (fun i _ => (hbulk i).2)
      _ = _ := by simp
  have hs : τ ≤ ∑ i, ℓ i ∧ (∑ i, ℓ i) ≤ 4 * τ := by
    rw [Fin.sum_univ_castSucc]
    constructor <;> linarith [htop.1, htop.2]
  have hfloor := Nat.floor_le (show 0 ≤ ∑ i, ℓ i by linarith [hs.1])
  have hnext := Nat.lt_floor_add_one (∑ i, ℓ i)
  exact ⟨by linarith [hs.1], hfloor.trans hs.2⟩

theorem eventual_bulk_word_small (α z : ℝ) (hα : 0 < α) (hz : 0 ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (V U τ : ℝ),
      (m : ℝ) ≤ z * L → V + α * L ≤ U → Real.exp U ≤ τ →
      (m : ℝ) * Real.exp V ≤ τ := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left z).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with L hbound hL m V U τ hm hVU hτ
  have hze : z * L ≤ Real.exp (α * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz hL),
      abs_of_pos (Real.exp_pos _), one_mul] using hbound
  calc
    (m : ℝ) * Real.exp V ≤ (z * L) * Real.exp V :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ ≤ Real.exp (α * L) * Real.exp V :=
      mul_le_mul_of_nonneg_right hze (Real.exp_pos _).le
    _ = Real.exp (V + α * L) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hVU
    _ ≤ τ := hτ

end Ostmann

end OAI
