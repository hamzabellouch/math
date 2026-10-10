import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The exact number of natural numbers below `N` in one residue class. -/
theorem card_range_zmod_eq {d : ℕ} [NeZero d] (N : ℕ) (r : ZMod d) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r)).card =
      N / d + if r.val < N % d then 1 else 0 := by
  have hd : 0 < d := NeZero.pos d
  have he : (Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r) =
      (Finset.range N).filter (fun n => Nat.ModEq d n r.val) := by
    apply Finset.filter_congr
    intro n hn
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.natCast_eq_natCast_iff n r.val d)
  rw [he, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card N hd r.val, Nat.mod_eq_of_lt r.val_lt]

/-- Exact quotient/remainder decomposition for any collection of residues. -/
theorem card_range_zmod_mem {d : ℕ} [NeZero d] (N : ℕ) (S : Finset (ZMod d)) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card =
      (N / d) * S.card + (S.filter (fun r => r.val < N % d)).card := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.range N) S
    (fun n : ℕ => (n : ZMod d))]
  simp_rw [card_range_zmod_eq]
  rw [Finset.sum_add_distrib]
  simp [mul_comm]

/-- The elementary progression-counting error is at most the number of
residue classes, uniformly in the interval length and modulus. -/
theorem abs_card_range_zmod_mem_sub {d : ℕ} [NeZero d]
    (N : ℕ) (S : Finset (ZMod d)) :
    |(((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card : ℝ) -
      (N : ℝ) * S.card / d| ≤ (S.card : ℝ) := by
  classical
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N (NeZero.pos d)
  have hq : (N : ℝ) = (N / d : ℕ) * (d : ℝ) + (N % d : ℕ) := by
    exact_mod_cast (show N = (N / d) * d + N % d by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm)
  have hs : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ (S.filter (fun r => r.val < N % d)).card := Nat.cast_nonneg _
  have hts : ((S.filter (fun r => r.val < N % d)).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_filter_le S (fun r => r.val < N % d)
  have hfrac0 : (0 : ℝ) ≤ (N % d : ℕ) / d := by positivity
  have hfrac1 : ((N % d : ℕ) : ℝ) / d ≤ 1 := (div_le_one hd).2 hr.le
  have hmain : (N : ℝ) * S.card / d =
      (N / d : ℕ) * (S.card : ℝ) + ((N % d : ℕ) : ℝ) / d * S.card := by
    rw [hq]
    field_simp
  rw [card_range_zmod_mem, Nat.cast_add, Nat.cast_mul, hmain]
  rw [abs_le]
  constructor <;> nlinarith

end Problem337

end

end OAI
