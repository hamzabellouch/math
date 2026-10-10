import Mathlib.Data.Int.CardIntervalMod
import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicAbel

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.IntegerCell
open scoped BigOperators
open PrimeProgression

def residueIndicator (M : ℕ) (a : ZMod M) (n : ℕ) : ℝ :=
  if (n : ZMod M) = a then 1 else 0

theorem residue_eq_modEq (M : ℕ) [NeZero M] (a : ZMod M) (n : ℕ) :
    (n : ZMod M) = a ↔ Nat.ModEq M n a.val := by
  simpa only [ZMod.natCast_zmod_val, Nat.ModEq] using ZMod.natCast_eq_natCast_iff' n a.val M

theorem residue_range_count (M : ℕ) [NeZero M] (a : ZMod M) (N : ℕ) :
    ∑ n ∈ Finset.range N, residueIndicator M a n =
      (N/M : ℕ) + if a.val % M < N % M then (1 : ℝ) else 0 := by
  have hM : 0 < M := Nat.pos_of_neZero M
  have he : (∑ n ∈ Finset.range N, residueIndicator M a n) =
      (N.count (fun n => Nat.ModEq M n a.val) : ℝ) := by
    rw [Nat.count_eq_card_filter_range]
    simp only [residueIndicator, residue_eq_modEq]
    simp
  rw [he, Nat.count_modEq_card N hM a.val, Nat.cast_add]
  split_ifs <;> norm_num

theorem cumulative_residue_error (M : ℕ) [NeZero M] (a : ZMod M)
    (x : ℝ) (hx : 0 ≤ x) :
    |cumulativeSum (residueIndicator M a) x - x/(M : ℝ)| ≤ 2 := by
  have hM : 0 < M := Nat.pos_of_neZero M
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hf : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hxf : x < (⌊x⌋₊ : ℝ)+1 := Nat.lt_floor_add_one x
  have hrem : (((⌊x⌋₊+1)%M : ℕ) : ℝ) < M := by exact_mod_cast Nat.mod_lt (⌊x⌋₊+1) hM
  have hrem0 : (0 : ℝ) ≤ (((⌊x⌋₊+1)%M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hquot : (((⌊x⌋₊+1)/M : ℕ) : ℝ)*(M : ℝ)+(((⌊x⌋₊+1)%M : ℕ) : ℝ) =
      (⌊x⌋₊ : ℝ)+1 := by
    exact_mod_cast (show (⌊x⌋₊+1)/M*M+(⌊x⌋₊+1)%M=⌊x⌋₊+1 by
      simpa only [Nat.mul_comm] using Nat.div_add_mod (⌊x⌋₊+1) M)
  have hid : cumulativeSum (residueIndicator M a) x =
      (((⌊x⌋₊+1)/M : ℕ) : ℝ) + if a.val%M < (⌊x⌋₊+1)%M then 1 else 0 := by
    unfold cumulativeSum
    rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.range_eq_Ico]
    exact residue_range_count M a (⌊x⌋₊+1)
  rw [hid]
  split_ifs <;> apply abs_le.mpr <;> constructor
  all_goals
    have hdiv : x/(M : ℝ)*(M : ℝ) = x := div_mul_cancel₀ x hMR.ne'
    nlinarith

end Ostmann.Arithmetic.IntegerCell
end

end OAI
