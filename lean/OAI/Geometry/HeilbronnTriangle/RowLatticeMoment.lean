import OAI.Geometry.HeilbronnTriangle.PairingMoment
import OAI.Geometry.HeilbronnTriangle.RowPairingDivisor

namespace OAI


namespace Problem355.LatticeMoment

open RowPairingDivisor RowLattice DiagonalStabilizer

theorem matrix_pairing_divisor_moment
    (S : Finset (Fin 3 → ℤ)) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R)
    (hbe : b ≤ e) (hek : e ≤ k)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hA : (A.map fun z : ℤ => (z : ZMod (B ^ k))) =
      (P : Matrix _ _ _) * diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
        (Q : Matrix _ _ _))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1) :
    ∑ x ∈ S, (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  apply cubic_divisor_moment_of_diagonal_form S
    (matrixPairingDivisor (B ^ k) A) A B R b e k hB hR hek P Q hA hbox
  · intro x hx
    obtain ⟨z, hz⟩ := hprimitive x hx
    exact (matrixPairingDivisor_pos_and_dvd B k b e hB.pos hbe A P Q hA x z hz).2
  · intro x hx i
    exact matrixPairingDivisor_dvd_mulVec (B ^ k) A x i

theorem matrix_pairing_divisor_moment_index
    (S : Finset (Fin 3 → ℤ)) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R)
    (hbe : b ≤ e) (hek : e ≤ k)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hA : (A.map fun z : ℤ => (z : ZMod (B ^ k))) =
      (P : Matrix _ _ _) * diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
        (Q : Matrix _ _ _))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1) :
    ∑ x ∈ S, (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 *
        ((integerRowLattice (B ^ k) (A.map fun z : ℤ => (z : ZMod (B ^ k)))).index : ℝ) := by
  let : NeZero B := ⟨hB.ne_zero⟩
  rw [integerRowLattice_index_prime_power B k b e (hbe.trans hek) hek _ P Q hA]
  push_cast
  rw [← pow_add]
  exact matrix_pairing_divisor_moment S A B R b e k hB hR hbe hek P Q hA hbox hprimitive

theorem matrix_pairing_divisor_cube_div_index_le
    (A : Matrix (Fin 3) (Fin 3) ℤ) (x z : Fin 3 → ℤ)
    (B b e k : ℕ) (hB : B.Prime) (hbe : b ≤ e) (hek : e ≤ k)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hA : (A.map fun z : ℤ => (z : ZMod (B ^ k))) =
      (P : Matrix _ _ _) * diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
        (Q : Matrix _ _ _))
    (hprimitive : dotProduct x z = 1) :
    (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 /
      ((integerRowLattice (B ^ k) (A.map fun z : ℤ => (z : ZMod (B ^ k)))).index : ℝ) ≤
        ((B : ℝ) ^ k) ^ 2 := by
  let : NeZero B := ⟨hB.ne_zero⟩
  rw [integerRowLattice_index_prime_power B k b e (hbe.trans hek) hek _ P Q hA]
  push_cast
  apply divisor_cube_div_index_le_modulus_sq B b e k _ hB.pos hek
  exact (matrixPairingDivisor_pos_and_dvd B k b e hB.pos hbe A P Q hA x z hprimitive).2

theorem matrix_pairing_divisor_moment_index_real
    (S : Finset (Fin 3 → ℤ)) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (B b e k : ℕ) (R : ℝ) (hB : B.Prime) (hR : (B : ℝ) ^ e ≤ R)
    (hbe : b ≤ e) (hek : e ≤ k)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hA : (A.map fun z : ℤ => (z : ZMod (B ^ k))) =
      (P : Matrix _ _ _) * diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
        (Q : Matrix _ _ _))
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)| ≤ R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1) :
    ∑ x ∈ S, (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 ≤
      128 * R ^ 3 *
        ((integerRowLattice (B ^ k) (A.map fun z : ℤ => (z : ZMod (B ^ k)))).index : ℝ) := by
  have hR0 : 0 ≤ R := (pow_nonneg (Nat.cast_nonneg B) e).trans hR
  have hfloor : B ^ e ≤ ⌊R⌋₊ := Nat.le_floor (by simpa only [Nat.cast_pow] using hR)
  have hbox' : ∀ x ∈ S, ∀ i, -(⌊R⌋₊ : ℤ) ≤ x i ∧ x i ≤ ⌊R⌋₊ := by
    intro x hx i
    have hcast : ((x i).natAbs : ℝ) = |(x i : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (x i))
    have hn : (x i).natAbs ≤ ⌊R⌋₊ := Nat.le_floor (hcast ▸ hbox x hx i)
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  have hm := matrix_pairing_divisor_moment_index S A B ⌊R⌋₊ b e k hB hfloor
    hbe hek P Q hA hbox' hprimitive
  refine hm.trans ?_
  gcongr
  exact Nat.floor_le hR0

theorem matrix_pairing_divisor_shell_moment
    (S : Finset (Fin 3 → ℤ)) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (B b e k : ℕ) (R : ℝ) (hB : B.Prime) (hR : (B : ℝ) ^ e ≤ R)
    (hbe : b ≤ e) (hek : e ≤ k)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hA : (A.map fun z : ℤ => (z : ZMod (B ^ k))) =
      (P : Matrix _ _ _) * diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
        (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S,
      ‖(WithLp.toLp 2 (fun i => (x i : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 * R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1) :
    ∑ x ∈ S, (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 ≤
      1024 * R ^ 3 *
        ((integerRowLattice (B ^ k) (A.map fun z : ℤ => (z : ZMod (B ^ k)))).index : ℝ) := by
  have hR0 : 0 ≤ R := (pow_nonneg (Nat.cast_nonneg B) e).trans hR
  have hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)| ≤ 2 * R := by
    intro x hx i
    have hc := PiLp.norm_apply_le
      (WithLp.toLp 2 (fun l => (x l : ℝ)) : EuclideanSpace ℝ (Fin 3)) i
    have hc' : |(x i : ℝ)| ≤
        ‖(WithLp.toLp 2 (fun l => (x l : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ := by
      simpa only [WithLp.ofLp_toLp, Real.norm_eq_abs] using hc
    exact hc'.trans (hnorm x hx)
  have hm := matrix_pairing_divisor_moment_index_real S A B b e k (2 * R) hB
    (by linarith) hbe hek P Q hA hbox hprimitive
  convert hm using 1; ring

end Problem355.LatticeMoment

end OAI
