import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

namespace OAI

/-! Harary–Hill arithmetic, residue-page definitions, and the even-order deletion inequality. -/

section

/-! The Harary–Hill formula and two-page crossing counts.

-/

open scoped BigOperators
noncomputable section
namespace Paper170

/-- The integer in the Harary–Hill formula. -/
def hill (n : ℕ) : ℕ :=
  (n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2)) / 4

/-- The two contiguous residue blocks used by the explicit drawing. -/
def residueColor (n r : ℕ) : Bool := decide (r % n < n / 2)

/-- Increasing four-tuples whose alternating edges occupy the same page. -/
def crossingTuples (n : ℕ) : Finset (Fin 4 → Fin n) := by
  classical
  exact Finset.univ.filter (fun v => StrictMono v ∧
    residueColor n ((v 0).val + (v 2).val) =
      residueColor n ((v 1).val + (v 3).val))

/-- Residues with the same color after a cyclic shift by k. -/
def sameColorResidues (n k : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun r => residueColor n r = residueColor n (r + k))

/-- Cyclic starting points and the first two positive gaps in the source count. -/
def sameColorGapTuples (n k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range n) ×ˢ ((Finset.Icc 1 (k - 1)) ×ˢ (Finset.Icc 1 (n - k - 1)))).filter
    (fun v => residueColor n (2 * v.1 + v.2.1 + v.2.2) =
      residueColor n (2 * v.1 + v.2.1 + v.2.2 + k))

/-- Starting labels producing a prescribed diagonal-sum residue. -/
def residueFiber (n b r : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a => (2 * a + b) % n = r)

/-- One parity class of the same-color residues. -/
def sameColorResiduesParity (n k p : ℕ) : Finset ℕ :=
  (sameColorResidues n k).filter (fun r => r % 2 = p)

/-- One parity class of the first-gap choices after a fixed offset. -/
def firstGapParity (k b p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (k - 1)).filter (fun g => (g + b) % 2 = p)

/-- The polynomial whose finite difference evaluates the crossing sum. -/
def crossingAntiderivative (n k : ℤ) : ℤ :=
  k * (k - 1) * (n - k - 1) * (n - k - 2)

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem crossingAntiderivative_sub (n k : ℤ) :
    crossingAntiderivative n k - crossingAntiderivative n (k - 1) =
      2 * (k - 1) * (n - k - 1) * (n - 2 * k) := by
  unfold crossingAntiderivative
  ring

theorem hill_numerator_dvd (n : ℕ) :
    4 ∣ n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  have h₂ : (n - 2) / 2 = n / 2 - 1 := by omega
  have h₃ : (n - 3) / 2 = (n - 1) / 2 - 1 := by omega
  rw [h₂, h₃]
  convert Nat.mul_dvd_mul (Nat.two_dvd_mul_sub_one (n / 2))
    (Nat.two_dvd_mul_sub_one ((n - 1) / 2)) using 1
  ring

theorem hill_even (s : ℕ) : hill (2 * s) = s * (s - 1) ^ 2 * (s - 2) / 4 := by
  have h₁ : (2 * s - 1) / 2 = s - 1 := by omega
  have h₂ : (2 * s - 2) / 2 = s - 1 := by omega
  have h₃ : (2 * s - 3) / 2 = s - 2 := by omega
  simp only [hill, Nat.mul_div_right s (by decide : 0 < 2), h₁, h₂, h₃]
  congr 1
  ring

theorem hill_odd (s : ℕ) : hill (2 * s + 1) = (s.choose 2) ^ 2 := by
  have h₀ : (2 * s + 1) / 2 = s := by omega
  have h₁ : (2 * s + 1 - 1) / 2 = s := by omega
  have h₂ : (2 * s + 1 - 2) / 2 = s - 1 := by omega
  have h₃ : (2 * s + 1 - 3) / 2 = s - 1 := by omega
  have hdiv := Nat.two_dvd_mul_sub_one s
  obtain ⟨a, ha⟩ := hdiv
  rw [hill, h₀, h₁, h₂, h₃, Nat.choose_two_right]
  have hp : s * s * (s - 1) * (s - 1) = 4 * a ^ 2 := by nlinarith [ha]
  rw [hp, ha]
  simp

theorem hill_eq_floor_product {n : ℕ} (hn : 1 ≤ n) :
    (hill n : ℝ) = (1 / 4 : ℝ) * (⌊(n : ℝ) / 2⌋ : ℝ) *
      (⌊((n : ℝ) - 1) / 2⌋ : ℝ) * (⌊((n : ℝ) - 2) / 2⌋ : ℝ) *
      (⌊((n : ℝ) - 3) / 2⌋ : ℝ) := by
  by_cases hsmall : n < 3
  · interval_cases n <;> norm_num [hill]
  have hf (j : ℕ) (hj : j ≤ n) :
      (⌊((n : ℝ) - j) / 2⌋ : ℝ) = ((n - j) / 2 : ℕ) := by
    rw [← Nat.cast_sub hj, show (2 : ℝ) = ((2 : ℕ) : ℝ) by rfl,
      Int.floor_div_natCast, Int.floor_natCast]
    norm_cast
  rw [hill, Nat.cast_div (hill_numerator_dvd n) (by norm_num : (4 : ℝ) ≠ 0)]
  have hf₀ := hf 0 (by omega)
  have hf₁ := hf 1 (by omega)
  have hf₂ := hf 2 (by omega)
  have hf₃ := hf 3 (by omega)
  simp only [Nat.cast_zero, sub_zero, Nat.sub_zero] at hf₀
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at hf₁ hf₂ hf₃
  rw [hf₀, hf₁, hf₂, hf₃]
  push_cast
  ring

theorem crossing_sum_partial {n m : ℕ} (hn : 3 ≤ n) (hm : 2 * m ≤ n) :
    2 * ∑ k ∈ Finset.Icc 1 m, (k - 1) * (n - k - 1) * (n - 2 * k) =
      m * (m - 1) * (n - m - 1) * (n - m - 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), mul_add,
      ih (by omega)]
    by_cases hzero : m = 0
    · subst m; simp
    have hm₁ : 1 ≤ m := by omega
    zify
    simp (disch := omega) only [Nat.cast_sub, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
    ring

theorem crossing_sum_telescope {n : ℕ} (hn : 3 ≤ n) :
    (2 * ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k)) =
      (n / 2) * (n / 2 - 1) * (n - n / 2 - 1) * (n - n / 2 - 2) :=
  crossing_sum_partial hn (by omega)

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem cyclic_count_pairing {n : ℕ} (hn : 3 ≤ n) :
    (∑ k ∈ Finset.Icc 2 (n - 2),
      (k - 1) * (n - k - 1) * (n - 2 * min k (n - k))) =
      2 * ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k) := by
  let F : ℕ → ℕ := fun k => (k - 1) * (n - k - 1) * (n - 2 * min k (n - k))
  have hsym (k : ℕ) (hk : k ≤ n) : F (n - k) = F k := by
    dsimp [F]
    rw [Nat.sub_sub_self hk, min_comm]
    ring
  have hfull : (∑ k ∈ Finset.Icc 2 (n - 2), F k) = ∑ k ∈ Finset.Ico 1 n, F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk hnot
      simp only [Finset.mem_Ico, Finset.mem_Icc, not_and] at hk hnot
      have he : k = 1 ∨ k = n - 1 := by omega
      rcases he with rfl | rfl
      · simp [F]
      · have he : n - (n - 1) - 1 = 0 := by omega
        simp [F, he]
  have hsplit := Finset.sum_Ico_consecutive F (show 1 ≤ n / 2 + 1 by omega)
    (show n / 2 + 1 ≤ n by omega)
  have htail : (∑ k ∈ Finset.Ico (n / 2 + 1) n, F k) =
      ∑ k ∈ Finset.Ico 1 (n - n / 2), F k := by
    calc
      _ = ∑ k ∈ Finset.Ico (n / 2 + 1) n, F (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hsym k (by have := (Finset.mem_Ico.mp hk).2; omega)).symm
      _ = _ := by
        simpa only [Nat.add_sub_cancel_left, Nat.add_sub_add_right] using
          (Finset.sum_Ico_reflect F (n / 2 + 1) (m := n) (n := n) (by omega))
  have hlow : (∑ k ∈ Finset.Ico 1 (n - n / 2), F k) =
      ∑ k ∈ Finset.Ico 1 (n / 2 + 1), F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk hnot
      simp only [Finset.mem_Ico, not_and] at hk hnot
      have he : n = 2 * k := by omega
      subst n
      simp [F, show 2 * k - k = k by omega]
  have hterm : (∑ k ∈ Finset.Ico 1 (n / 2 + 1), F k) =
      ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    rw [min_eq_left (by have := (Finset.mem_Icc.mp hk).2; omega)]
  change (∑ k ∈ Finset.Icc 2 (n - 2), F k) = _
  rw [hfull, ← hsplit, htail, hlow, hterm]
  omega

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma four_mul_hill (n : ℕ) :
    4 * hill n = n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  exact Nat.mul_div_cancel' (hill_numerator_dvd n)

lemma four_mul_hill_even (s : ℕ) :
    4 * hill (2 * s) = s * (s - 1) ^ 2 * (s - 2) := by
  rw [four_mul_hill]
  have h0 : 2 * s / 2 = s := by omega
  have h1 : (2 * s - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 2) / 2 = s - 1 := by omega
  have h3 : (2 * s - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma four_mul_hill_preceding (s : ℕ) :
    4 * hill (2 * s - 1) = (s - 1) ^ 2 * (s - 2) ^ 2 := by
  rw [four_mul_hill]
  have h0 : (2 * s - 1) / 2 = s - 1 := by omega
  have h1 : (2 * s - 1 - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 1 - 2) / 2 = s - 2 := by omega
  have h3 : (2 * s - 1 - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma hill_deletion_relation (s : ℕ) :
    (2 * s - 4) * hill (2 * s) = 2 * s * hill (2 * s - 1) := by
  have hs : 2 * s - 4 = 2 * (s - 2) := by omega
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4)
  calc
    4 * ((2 * s - 4) * hill (2 * s)) =
        (2 * s - 4) * (4 * hill (2 * s)) := by ring
    _ = (2 * s - 4) * (s * (s - 1) ^ 2 * (s - 2)) := by rw [four_mul_hill_even]
    _ = 2 * s * ((s - 1) ^ 2 * (s - 2) ^ 2) := by rw [hs]; ring
    _ = 4 * (2 * s * hill (2 * s - 1)) := by rw [← four_mul_hill_preceding]; ring

lemma even_lower_bound_of_deletion (s c : ℕ) (hs : 3 ≤ s)
    (h : 2 * s * hill (2 * s - 1) ≤ (2 * s - 4) * c) : hill (2 * s) ≤ c := by
  rw [← hill_deletion_relation] at h
  have hp : 0 < 2 * s - 4 := by omega
  nlinarith

end Paper170

end
end

end OAI
