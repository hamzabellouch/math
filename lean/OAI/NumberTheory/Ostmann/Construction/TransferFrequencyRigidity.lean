import OAI.NumberTheory.Ostmann.Construction.TransferFrequencyRange

namespace OAI

/-! # Uniqueness of the two child frequencies and inserted pivot -/

namespace Ostmann

/-- Comparing two valid substitutions makes the child-frequency determinant
both divisible by the root frequency and too small to be nonzero. -/
theorem transfer_frequency_determinant_zero (L R P Q B K : ℕ) (s v w v' w' : ℤ)
    (hs : s ≠ 0) (hunit : IsCoprime s (R : ℤ))
    (hrel : v * R - w * L = s * P) (hrel' : v' * R - w' * L = s * Q)
    (hP : P ≤ K) (hQ : Q ≤ K) (hw : w.natAbs ≤ B) (hw' : w'.natAbs ≤ B)
    (hgap : 2 * K * B < R) : v * w' - v' * w = 0 := by
  let d := v * w' - v' * w
  let e := (P : ℤ) * w' - (Q : ℤ) * w
  have heq : (R : ℤ) * d = s * e := by
    dsimp [d, e]
    linear_combination w' * hrel - w * hrel'
  have hdiv : s ∣ d := hunit.dvd_of_dvd_mul_left ⟨e, heq⟩
  have heb : e.natAbs < R := by
    calc
      _ ≤ ((P : ℤ) * w').natAbs + ((Q : ℤ) * w).natAbs := Int.natAbs_sub_le _ _
      _ = P * w'.natAbs + Q * w.natAbs := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ K * B + K * B := Nat.add_le_add (Nat.mul_le_mul hP hw') (Nat.mul_le_mul hQ hw)
      _ = 2 * K * B := by ring
      _ < R := hgap
  by_contra hd
  have hd' : d ≠ 0 := hd
  have hle : s.natAbs ≤ d.natAbs := Int.natAbs_le_of_dvd_ne_zero hdiv hd'
  have ha := congrArg Int.natAbs heq
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at ha
  have hlt := Nat.mul_lt_mul_of_pos_left heb (Int.natAbs_pos.mpr hs)
  have hle' := Nat.mul_le_mul_left R hle
  nlinarith

/-- Coprimality with the frequencies rules out any nontrivial proportional
rescaling of the positive pivot. -/
theorem transfer_substitution_unique (L R P Q B K : ℕ) (s v w v' w' : ℤ)
    (hs : s ≠ 0) (hunit : IsCoprime s (R : ℤ))
    (hrel : v * R - w * L = s * P) (hrel' : v' * R - w' * L = s * Q)
    (hPpos : 0 < P) (hP : P ≤ K) (hQ : Q ≤ K)
    (hw : w.natAbs ≤ B) (hw' : w'.natAbs ≤ B)
    (hgap : 2 * K * B < R)
    (hPw : P.Coprime w.natAbs) (hQw : Q.Coprime w'.natAbs) :
    v = v' ∧ w = w' ∧ P = Q := by
  have hd := transfer_frequency_determinant_zero L R P Q B K s v w v' w'
    hs hunit hrel hrel' hP hQ hw hw' hgap
  have hcross : (P : ℤ) * w' = (Q : ℤ) * w := by
    have he : s * ((P : ℤ) * w' - (Q : ℤ) * w) = 0 := by
      calc
        _ = (R : ℤ) * (v * w' - v' * w) := by
          linear_combination -(w' * hrel - w * hrel')
        _ = 0 := by rw [hd, mul_zero]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)
  have hcrossNat := congrArg Int.natAbs hcross
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hcrossNat
  have hdPQ : P ∣ Q := hPw.dvd_of_dvd_mul_left (by
    rw [mul_comm w.natAbs Q, ← hcrossNat]
    exact dvd_mul_right P w'.natAbs)
  have hdQP : Q ∣ P := hQw.dvd_of_dvd_mul_left (by
    rw [mul_comm w'.natAbs P, hcrossNat]
    exact dvd_mul_right Q w.natAbs)
  have hPQ : P = Q := Nat.dvd_antisymm hdPQ hdQP
  have hwEq : w = w' := by
    rw [← hPQ] at hcross
    exact (mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hPpos) hcross).symm
  have hRpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hgap
  have hvEq : v = v' := by
    have he : v * (R : ℤ) = v' * (R : ℤ) := by
      rw [← hwEq, ← hPQ] at hrel'
      linear_combination hrel - hrel'
    exact mul_right_cancel₀ (by exact_mod_cast Nat.ne_of_gt hRpos) he
  exact ⟨hvEq, hwEq, hPQ⟩

end Ostmann

end OAI
