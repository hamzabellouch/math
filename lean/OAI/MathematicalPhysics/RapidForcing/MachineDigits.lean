import OAI.MathematicalPhysics.RapidForcing.Scales

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma radix_pair_lt {S R q T : ℕ} (hq : q < S) (hT : T < R) :
    q + S * T < S * R := by
  have h := Nat.mul_le_mul_left S (Nat.succ_le_of_lt hT)
  nlinarith

lemma replace_digit_lt {A T p j z' : ℕ} (hA : 0 < A) (hT : T < A ^ p)
    (hj : j < p) (hz : z' < A) :
    T - (T / A ^ j % A) * A ^ j + z' * A ^ j < A ^ p := by
  let Q := A ^ j
  let z := T / Q % A
  let U := T / (Q * A)
  let R := A ^ (p - (j + 1))
  have hQ : 0 < Q := pow_pos hA _
  have hf : A ^ p = (Q * A) * R := by
    dsimp [Q, R]
    rw [← pow_succ, ← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt hj)]
  have hU : U < R := by
    apply Nat.div_lt_of_lt_mul
    simpa only [hf] using hT
  have hlow : T % Q < Q := Nat.mod_lt _ hQ
  have hdec : T = (T % Q + (Q * A) * U) + z * Q := by
    have hh := Nat.mod_add_div T (Q * A)
    rw [Nat.mod_mul] at hh
    dsimp [z, U]
    nlinarith
  have hsub : T - z * Q = T % Q + (Q * A) * U := by omega
  change T - z * Q + z' * Q < A ^ p
  rw [hsub, hf]
  have hzm := Nat.mul_le_mul_right Q (Nat.succ_le_of_lt hz)
  have hUm := Nat.mul_le_mul_left (Q * A) (Nat.succ_le_of_lt hU)
  nlinarith

namespace ScaleData
variable (d : ScaleData)

lemma A_pos : 0 < d.A := pow_pos (by decide) _
lemma one_le_A : 1 ≤ d.A := d.A_pos
lemma S_pos : 0 < d.S := pow_pos (by decide) _
lemma P_pos (n : ℕ) : 0 < d.P n := pow_pos (by decide) _

lemma capacity_eq (n : ℕ) :
    d.capacity n = d.S * d.P n * d.A ^ (2 * n + d.B + 1) := by
  simp only [capacity, L, S, P, A, ← pow_add, ← pow_mul]
  congr 1

lemma head_lt_P (n : ℕ) : 2 * n < d.P n := by
  have hn := Nat.lt_two_pow_self (n := n)
  unfold P
  rw [pow_add]
  norm_num
  nlinarith

lemma tape_quotient_lt {n k : ℕ} (hk : k < d.capacity n) :
    k / (d.S * d.P n) < d.A ^ (2 * n + d.B + 1) := by
  apply Nat.div_lt_of_lt_mul
  rwa [d.capacity_eq] at hk

end ScaleData

namespace Machine
variable (M : Machine)

lemma alphabet_lt_A (w : M.Input) : M.symbols < (M.scaleData w).A := by
  exact lt_trans (Nat.lt_succ_self _) (Nat.lt_two_pow_self (n := M.symbols + 1))

lemma states_lt_S (w : M.Input) : M.states < (M.scaleData w).S := by
  exact lt_trans (Nat.lt_succ_self _) (Nat.lt_two_pow_self (n := M.states + 1))

lemma instruction_range {q z : ℕ} (hq : q < M.states) (hz : z < M.symbols) :
    (M.instruction q z).1 ≤ M.states ∧
      (M.instruction q z).2.1 < M.symbols := by
  unfold instruction
  simp only [dite_eq_left hq, dite_eq_left hz]
  cases h : M.transition ⟨q, hq⟩ ⟨z, hz⟩ with
  | none => exact ⟨le_rfl, hz⟩
  | some v => exact ⟨v.1.isLt.le, v.2.1.isLt⟩

theorem nextDigit_lt (w : M.Input) {n k : ℕ}
    (hk : k < (M.scaleData w).capacity n) :
    M.nextDigit (M.scaleData w) n k < (M.scaleData w).capacity (n + 1) := by
  let d := M.scaleData w
  let q := k % d.S
  let j := (k / d.S) % d.P n
  let T := k / (d.S * d.P n)
  let z := T / d.A ^ j % d.A
  change (if q < M.states ∧ j ≤ 2 * n ∧ z < M.symbols then
    (M.instruction q z).1 + d.S * (j + (M.instruction q z).2.2.val +
      d.P (n + 1) * d.A * (T - z * d.A ^ j + (M.instruction q z).2.1 * d.A ^ j))
    else 0) < d.capacity (n + 1)
  split_ifs with h
  · obtain ⟨hq, hj, hz⟩ := h
    have hr := M.instruction_range hq hz
    have hq' : (M.instruction q z).1 < d.S :=
      lt_of_le_of_lt hr.1 (M.states_lt_S w)
    have hz' : (M.instruction q z).2.1 < d.A :=
      lt_trans hr.2 (M.alphabet_lt_A w)
    have hjp : j < 2 * n + d.B + 1 := by omega
    have hT : T < d.A ^ (2 * n + d.B + 1) := d.tape_quotient_lt hk
    have hnew := replace_digit_lt d.A_pos hT hjp hz'
    have hhead : j + (M.instruction q z).2.2.val < d.P (n + 1) := by
      have := (M.instruction q z).2.2.isLt
      have := d.head_lt_P (n + 1)
      omega
    have htape :
        d.A * (T - z * d.A ^ j + (M.instruction q z).2.1 * d.A ^ j) <
          d.A ^ (2 * (n + 1) + d.B + 1) := by
      have hmul := Nat.mul_lt_mul_of_pos_left hnew d.A_pos
      have hpow : d.A * d.A ^ (2 * n + d.B + 1) ≤
          d.A ^ (2 * (n + 1) + d.B + 1) := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right d.one_le_A (by omega)
      exact lt_of_lt_of_le hmul hpow
    have hinner := radix_pair_lt hhead htape
    have houter := radix_pair_lt hq' hinner
    rw [d.capacity_eq]
    convert houter using 1 <;> ring
  · exact d.capacity_pos _

end Machine
end RapidForcing

end OAI
