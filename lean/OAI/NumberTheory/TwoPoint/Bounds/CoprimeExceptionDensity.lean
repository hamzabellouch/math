import OAI.NumberTheory.TwoPoint.Bounds.ResidueCounts
import OAI.NumberTheory.TwoPoint.Basic
import Mathlib.Algebra.BigOperators.Field

namespace OAI

/-! The finite coprimality-exception count used when extracting a fixed
divisor from two multiplicative functions. No independence between the
two residue conditions is assumed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def shiftedDivisorCount (p a Y : ℕ) : ℕ :=
  ∑ v ∈ range Y, if p ∣ a + v then 1 else 0

lemma shiftedDivisorCount_eq_residueCount (p a Y : ℕ) [NeZero p] :
    shiftedDivisorCount p a Y = residueCount (a : ZMod p) Y 0 := by
  unfold shiftedDivisorCount residueCount
  simp only [← Nat.cast_add, ZMod.natCast_eq_zero_iff]

lemma shiftedDivisorCount_le (p a Y : ℕ) (hp : 0 < p) :
    (shiftedDivisorCount p a Y : ℝ) ≤ (Y : ℝ) / p + 1 := by
  let _ : NeZero p := ⟨hp.ne'⟩
  rw [shiftedDivisorCount_eq_residueCount]
  have hb := (abs_le.mp (residueCount_discrepancy (a : ZMod p) 0 Y)).2
  linarith

def coprimeExceptionCount (u d Y : ℕ) : ℕ :=
  ∑ v ∈ range Y, if ¬u.Coprime ((v + 1) * (v + 1 + d)) then 1 else 0

lemma coprimeExceptionCount_le_divisorCounts (u d Y : ℕ) (P : Finset ℕ)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    coprimeExceptionCount u d Y ≤
      ∑ p ∈ P, (shiftedDivisorCount p 1 Y + shiftedDivisorCount p (1 + d) Y) := by
  unfold coprimeExceptionCount shiftedDivisorCount
  calc
    _ ≤ ∑ v ∈ range Y, ∑ p ∈ P,
        ((if p ∣ 1 + v then 1 else 0) + (if p ∣ 1 + d + v then 1 else 0)) := by
      apply sum_le_sum
      intro v _
      by_cases hv : u.Coprime ((v + 1) * (v + 1 + d))
      · calc
          _ = 0 := ite_eq_right (fun hnot => hnot hv)
          _ ≤ _ := Nat.zero_le _
      · simp only [hv, not_false_eq_true, ite_true]
        obtain ⟨p, hp, hpu, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hv
        have hpP := hcover p hp hpu
        have hsingle :
            ((if p ∣ 1 + v then 1 else 0) + (if p ∣ 1 + d + v then 1 else 0)) ≤
              ∑ p ∈ P, ((if p ∣ 1 + v then 1 else 0) +
                (if p ∣ 1 + d + v then 1 else 0)) :=
          single_le_sum (f := fun p : ℕ =>
            ((if p ∣ 1 + v then 1 else 0) + (if p ∣ 1 + d + v then 1 else 0) : ℕ))
            (fun _ _ => Nat.zero_le _) hpP
        apply le_trans _ hsingle
        rcases hp.dvd_mul.mp hpn with hpn | hpn
        · have ht : p ∣ 1 + v := by simpa only [Nat.add_comm] using hpn
          simp only [ht, ite_true]
          omega
        · have ht : p ∣ 1 + d + v := by
            convert hpn using 1
            omega
          simp only [ht, ite_true]
          omega
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      exact sum_add_distrib

theorem coprimeExceptionCount_bound (u d Y : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    (coprimeExceptionCount u d Y : ℝ) ≤
      2 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 2 * P.card := by
  have hnat := coprimeExceptionCount_le_divisorCounts u d Y P hcover
  calc
    _ ≤ ∑ p ∈ P, ((shiftedDivisorCount p 1 Y : ℝ) +
        (shiftedDivisorCount p (1 + d) Y : ℝ)) := by exact_mod_cast hnat
    _ ≤ ∑ p ∈ P, (2 * (Y : ℝ) * (1 / (p : ℝ)) + 2) := by
      apply sum_le_sum
      intro p hp
      have h₁ := shiftedDivisorCount_le p 1 Y (hP p hp).pos
      have h₂ := shiftedDivisorCount_le p (1 + d) Y (hP p hp).pos
      calc
        _ ≤ ((Y : ℝ) / p + 1) + ((Y : ℝ) / p + 1) := add_le_add h₁ h₂
        _ = _ := by ring
    _ = _ := by rw [sum_add_distrib, mul_sum]; simp [mul_comm]

theorem coprimeExceptionDensity_bound (u d Y : ℕ) (hY : 0 < Y) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    (coprimeExceptionCount u d Y : ℝ) / Y ≤
      2 * (∑ p ∈ P, 1 / (p : ℝ)) + 2 * P.card / (Y : ℝ) := by
  have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
  apply (div_le_iff₀ hY').mpr
  have hb := coprimeExceptionCount_bound u d Y P hP hcover
  convert hb using 1
  field_simp

end TwoPointCorrelations

end OAI
