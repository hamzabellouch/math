import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticBounds

namespace OAI

section

namespace KS.W30

theorem zeroPivot_coefficient_parts_bound (q r : ℚ) (H : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ H) (hqden : q.den ≤ 2 ^ H)
    (hrnum : r.num.natAbs ≤ 2 ^ H) (hrden : r.den ≤ 2 ^ H) :
    (-(q + 1) / (2 * r)).num.natAbs ≤ 2 ^ (3 * H + 3) ∧
      (-(q + 1) / (2 * r)).den ≤ 2 ^ (3 * H + 3) := by
  have ha := add_parts_le_two_pow q 1 H 0 hqnum hqden (by norm_num) (by norm_num)
  have han : (-(q + 1)).num.natAbs ≤ 2 ^ (H + 1) := by
    simpa only [Rat.neg_num, Int.natAbs_neg, Nat.add_zero] using ha.1
  have had : (-(q + 1)).den ≤ 2 ^ (H + 1) := by
    rw [Rat.neg_den]
    have had' : (q + 1).den ≤ 2 ^ H := by simpa only [Nat.add_zero] using ha.2
    exact had'.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ H))
  have hm := mul_parts_le_two_pow 2 r 1 H (by norm_num) (by norm_num) hrnum hrden
  have hd := div_parts_le_two_pow (-(q + 1)) (2 * r) (H + 1) (1 + H)
    han had hm.1 hm.2
  have hp : 2 ^ (H + 1 + (1 + H)) ≤ 2 ^ (3 * H + 3) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  exact ⟨hd.1.trans hp, hd.2.trans hp⟩

theorem sparse_pair_common_height {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (z : ℚ) (E : ℕ) (hznum : z.num.natAbs ≤ 2 ^ E) (hzden : z.den ≤ 2 ^ E) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 2 ^ E ∧ ∃ Z : Fin n → ℤ,
      (∀ k, (Pi.single i z + Pi.single j 1 : Fin n → ℚ) k = (Z k : ℚ) / D) ∧
      ∀ k, (Z k).natAbs ≤ 2 ^ E := by
  let Z : Fin n → ℤ := Pi.single i z.num + Pi.single j (z.den : ℤ)
  refine ⟨z.den, z.den_pos, hzden, Z, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      simp [Z, hij, Rat.num_div_den]
    · by_cases hkj : k = j
      · subst k
        simp [Z, Ne.symm hij, z.den_nz]
      · simp [Z, hki, hkj]
  · intro k
    by_cases hki : k = i
    · subst k
      simpa [Z, Pi.single_apply, hij, Ne.symm hij] using hznum
    · by_cases hkj : k = j
      · subst k
        simpa [Z, Pi.single_apply, hij, Ne.symm hij] using hzden
      · simp [Z, hki, hkj]

theorem zeroPivot_pair_common_height {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (q r : ℚ) (H : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ H) (hqden : q.den ≤ 2 ^ H)
    (hrnum : r.num.natAbs ≤ 2 ^ H) (hrden : r.den ≤ 2 ^ H) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 2 ^ (3 * H + 3) ∧ ∃ Z : Fin n → ℤ,
      (∀ k, (Pi.single i (-(q + 1) / (2 * r)) + Pi.single j 1 : Fin n → ℚ) k =
        (Z k : ℚ) / D) ∧
      ∀ k, (Z k).natAbs ≤ 2 ^ (3 * H + 3) := by
  have h := zeroPivot_coefficient_parts_bound q r H hqnum hqden hrnum hrden
  exact sparse_pair_common_height i j hij _ _ h.1 h.2

end KS.W30

end

end OAI
