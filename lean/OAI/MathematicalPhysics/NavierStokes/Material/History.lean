import OAI.MathematicalPhysics.NavierStokes.Material.Scales
import OAI.MathematicalPhysics.NavierStokes.Material.Encoding

namespace OAI

namespace Alternating.Memory
open scoped BigOperators
open Finset

theorem old_block_integer {b N : ℕ} (hb : 0 < b) {j a : ℕ}
    (c : Block b (width N j)) (ha : scale N j + (1 + 2 * width N j) ≤ a) :
    ∃ k : ℤ, (b : ℝ) ^ a * (epsilon b N j * c.code) = k := by
  obtain ⟨k, hk⟩ := c.code_denominator hb
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  let d := 1 + 2 * width N j
  have hexp : a = a - (scale N j + d) + (scale N j + d) :=
    (Nat.sub_add_cancel ha).symm
  refine ⟨(b : ℤ) ^ (a - (scale N j + d)) * k, ?_⟩
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [← hk]
  conv_lhs => rw [hexp]
  simp only [pow_add, epsilon, inv_pow]
  dsimp [d]
  field_simp
  rw [pow_add, pow_one]
  ring

noncomputable def history (b N : ℕ) (C : ∀ n, Block b (width N n)) (parity n : ℕ) : ℝ :=
  ∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = parity), epsilon b N j * (C j).code

noncomputable def donor (b N : ℕ) (C : ∀ n, Block b (width N n)) (n : ℕ) : ℝ :=
  history b N C (n % 2) n

theorem donor_scaled {b N : ℕ} (hb : 2 ≤ b)
    (C : ∀ n, Block b (width N n)) (n : ℕ) :
    ∃ k : ℤ, (b : ℝ) ^ scale N n * donor b N C n = k + (C n).code := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hsum : ∀ j ∈ (range n).filter (fun j => j % 2 = n % 2),
      ∃ k : ℤ, (b : ℝ) ^ scale N n * (epsilon b N j * (C j).code) = k := by
    intro j hj
    have hjn : j < n := mem_range.1 (mem_filter.1 hj).1
    apply old_block_integer (by omega) (C j)
    have := old_block_gap N hjn
    omega
  choose! k hk using hsum
  refine ⟨∑ j ∈ (range n).filter (fun j => j % 2 = n % 2), k j, ?_⟩
  simp only [donor, history, range_add_one, filter_insert, ite_true]
  rw [sum_insert (by simp), mul_add, mul_sum]
  have hlast : (b : ℝ) ^ scale N n * (epsilon b N n * (C n).code) = (C n).code := by
    simp [epsilon, inv_pow, hb0]
  rw [hlast, Int.cast_sum]
  rw [sum_congr rfl (fun j hj => hk j hj)]
  ring

theorem periodic_integer_add {P : ℝ → ℝ} (hP : Function.Periodic P 1)
    (k : ℤ) (a : ℝ) : P ((k : ℝ) + a) = P a := by
  simpa [add_comm] using (hP.int_mul k) a

theorem read_exact {b N : ℕ} (hb : 2 ≤ b) (C : ∀ n, Block b (width N n))
    {P : ℝ → ℝ} (hperiod : Function.Periodic P 1)
    (hid : ∀ a ∈ Set.Icc 0 (tailBound b), P a = a) (n : ℕ) :
    P ((b : ℝ) ^ scale N n * donor b N C n) = (C n).code ∧
    P ((b : ℝ) ^ (scale N n + 1 + width N n) * donor b N C n) = (C n).rightCode ∧
    P ((b : ℝ) ^ (scale N n + 1) * donor b N C n) -
      (b : ℝ)⁻¹ ^ width N n *
        P ((b : ℝ) ^ (scale N n + 1 + width N n) * donor b N C n) = (C n).leftCode := by
  have hbpos : 0 < b := by omega
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
  obtain ⟨k, hk⟩ := donor_scaled hb C n
  have hfirst : P ((b : ℝ) ^ scale N n * donor b N C n) = (C n).code := by
    rw [hk, periodic_integer_add hperiod, hid _ ⟨(C n).code_nonneg, (C n).code_le hb⟩]
  have htail : (b : ℝ) ^ (scale N n + 1) * donor b N C n =
      ((b : ℤ) * k + (C n).stateDigit : ℤ) +
        ((C n).leftCode + (b : ℝ)⁻¹ ^ width N n * (C n).rightCode) := by
    rw [pow_succ]
    have he : (b : ℝ) ^ scale N n * b * donor b N C n =
        b * ((b : ℝ) ^ scale N n * donor b N C n) := by ring
    rw [he, hk, (C n).code_formula hbpos]
    push_cast
    field_simp
    ring
  have hleft := (C n).left_denominator hbpos
  obtain ⟨kl, hkl⟩ := hleft
  have hright : (b : ℝ) ^ (scale N n + 1 + width N n) * donor b N C n =
      ((b : ℤ) ^ width N n * ((b : ℤ) * k + (C n).stateDigit) + kl : ℤ) +
        (C n).rightCode := by
    rw [pow_add]
    have he : (b : ℝ) ^ (scale N n + 1) * (b : ℝ) ^ width N n * donor b N C n =
        (b : ℝ) ^ width N n * ((b : ℝ) ^ (scale N n + 1) * donor b N C n) := by ring
    rw [he, htail, mul_add]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [← hkl]
    simp [mul_add, ← mul_assoc, inv_pow, hb0, add_assoc]
  have hreadR : P ((b : ℝ) ^ (scale N n + 1 + width N n) * donor b N C n) =
      (C n).rightCode := by
    rw [hright, periodic_integer_add hperiod, hid _ ((C n).right_mem hb)]
  refine ⟨hfirst, hreadR, ?_⟩
  rw [htail, periodic_integer_add hperiod, hid _ ((C n).tail_mem hb), hreadR]
  ring

end Alternating.Memory

end OAI
