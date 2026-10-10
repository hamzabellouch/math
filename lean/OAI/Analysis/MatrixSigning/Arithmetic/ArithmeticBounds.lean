import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalBounds

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem mul_num_natAbs_le (q r : ℚ) :
    (q * r).num.natAbs ≤ q.num.natAbs * r.num.natAbs := by
  have heq : q * r = (q.num * r.num) /. ((q.den : ℤ) * r.den) := by
    simpa only [Rat.num_divInt_den] using
      (Rat.divInt_mul_divInt q.num r.num :
        q.num /. (q.den : ℤ) * (r.num /. (r.den : ℤ)) =
          (q.num * r.num) /. ((q.den : ℤ) * r.den))
  rw [heq]
  simpa only [Int.natAbs_mul] using
    divInt_num_natAbs_le (q.num * r.num) ((q.den : ℤ) * r.den)
      (mul_ne_zero (Int.natCast_ne_zero.mpr q.den_nz)
        (Int.natCast_ne_zero.mpr r.den_nz))

theorem mul_den_le (q r : ℚ) : (q * r).den ≤ q.den * r.den :=
  Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.mul_den_dvd q r)

theorem add_num_natAbs_le (q r : ℚ) :
    (q + r).num.natAbs ≤ q.num.natAbs * r.den + q.den * r.num.natAbs := by
  rw [Rat.add_num_den]
  apply le_trans (divInt_num_natAbs_le _ _
    (mul_ne_zero (Int.natCast_ne_zero.mpr q.den_nz)
      (Int.natCast_ne_zero.mpr r.den_nz)))
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
    Int.natAbs_add_le (q.num * r.den) ((q.den : ℤ) * r.num)

theorem add_den_le (q r : ℚ) : (q + r).den ≤ q.den * r.den :=
  Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.add_den_dvd q r)

theorem mul_parts_le_two_pow (q r : ℚ) (b c : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b)
    (hrnum : r.num.natAbs ≤ 2 ^ c) (hrden : r.den ≤ 2 ^ c) :
    (q * r).num.natAbs ≤ 2 ^ (b + c) ∧ (q * r).den ≤ 2 ^ (b + c) := by
  constructor
  · exact (mul_num_natAbs_le q r).trans (by
      simpa only [pow_add] using Nat.mul_le_mul hqnum hrnum)
  · exact (mul_den_le q r).trans (by
      simpa only [pow_add] using Nat.mul_le_mul hqden hrden)

theorem add_parts_le_two_pow (q r : ℚ) (b c : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b)
    (hrnum : r.num.natAbs ≤ 2 ^ c) (hrden : r.den ≤ 2 ^ c) :
    (q + r).num.natAbs ≤ 2 ^ (b + c + 1) ∧ (q + r).den ≤ 2 ^ (b + c) := by
  constructor
  · apply (add_num_natAbs_le q r).trans
    have h := Nat.add_le_add (Nat.mul_le_mul hqnum hrden) (Nat.mul_le_mul hqden hrnum)
    simpa only [pow_succ, pow_add, mul_two] using h
  · exact (add_den_le q r).trans (by
      simpa only [pow_add] using Nat.mul_le_mul hqden hrden)

theorem inv_parts_le_two_pow (q : ℚ) (b : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b) :
    q⁻¹.num.natAbs ≤ 2 ^ b ∧ q⁻¹.den ≤ 2 ^ b := by
  by_cases hz : q.num = 0
  · simp [Rat.num_inv, Rat.den_inv, hz, Nat.one_le_two_pow]
  · simpa only [Rat.num_inv, Rat.den_inv, hz, ite_false, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero hz, Int.natAbs_natCast, one_mul] using
      And.intro hqden hqnum

theorem div_parts_le_two_pow (q r : ℚ) (b c : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b)
    (hrnum : r.num.natAbs ≤ 2 ^ c) (hrden : r.den ≤ 2 ^ c) :
    (q / r).num.natAbs ≤ 2 ^ (b + c) ∧ (q / r).den ≤ 2 ^ (b + c) := by
  have hi := inv_parts_le_two_pow r c hrnum hrden
  simpa only [div_eq_mul_inv] using mul_parts_le_two_pow q r⁻¹ b c hqnum hqden hi.1 hi.2

theorem list_sum_parts_le_two_pow (xs : List ℚ) (b : ℕ)
    (hxs : ∀ q ∈ xs, q.num.natAbs ≤ 2 ^ b ∧ q.den ≤ 2 ^ b) :
    xs.sum.num.natAbs ≤ 2 ^ ((b + 1) * xs.length) ∧
      xs.sum.den ≤ 2 ^ ((b + 1) * xs.length) := by
  revert hxs
  induction xs with
  | nil => intro _; simp
  | cons q xs ih =>
      intro hxs
      have hq := hxs q (by simp)
      have ht := ih (fun r hr => hxs r (by simp [hr]))
      have ha := add_parts_le_two_pow q xs.sum b ((b + 1) * xs.length)
        hq.1 hq.2 ht.1 ht.2
      have he : b + (b + 1) * xs.length + 1 = (b + 1) * (xs.length + 1) := by ring
      simp only [List.sum_cons, List.length_cons]
      rw [← he]
      exact ⟨ha.1, ha.2.trans (Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.le_succ _))⟩

theorem list_prod_parts_le_two_pow (xs : List ℚ) (b : ℕ)
    (hxs : ∀ q ∈ xs, q.num.natAbs ≤ 2 ^ b ∧ q.den ≤ 2 ^ b) :
    xs.prod.num.natAbs ≤ 2 ^ (b * xs.length) ∧ xs.prod.den ≤ 2 ^ (b * xs.length) := by
  revert hxs
  induction xs with
  | nil => intro _; simp
  | cons q xs ih =>
      intro hxs
      have hq := hxs q (by simp)
      have ht := ih (fun r hr => hxs r (by simp [hr]))
      have ha := mul_parts_le_two_pow q xs.prod b (b * xs.length) hq.1 hq.2 ht.1 ht.2
      simpa only [List.prod_cons, List.length_cons, Nat.mul_succ, Nat.add_comm] using ha

end KS.W30

end

end OAI
