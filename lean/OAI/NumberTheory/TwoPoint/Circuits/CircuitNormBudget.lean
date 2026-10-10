import OAI.NumberTheory.TwoPoint.Circuits.CircuitExceptionBudget

namespace OAI

/-! A coarse uniform bound on the exceptional values of the polynomial.
For fixed depth its logarithm is polynomial in the sampling count and log size. -/

namespace TwoPointCorrelations.AC0Circuit

open Finset
open scoped Classical

theorem sampleNormBound_le {n : ℕ} (s : ℕ) (c : AC0Circuit n)
    (m : ℕ) (hm : c.size ≤ m) :
    c.sampleNormBound s ≤ (2 * ((m : ℝ) + 1) ^ 2) ^
      ((2 * (s * (Nat.log 2 m + 3)) + 2) ^ c.depth) := by
  induction c generalizing m with
  | literal i b =>
    simp only [sampleNormBound, depth, pow_zero, pow_one]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  | @andGate k c ih | @orGate k c ih =>
    have hm' : 1 + ∑ i, (c i).size ≤ m := hm
    have hsize (i : Fin k) : (c i).size ≤ m := by
      have hh := single_le_sum (fun j _ => Nat.zero_le (c j).size) (mem_univ i)
      omega
    have hcount : k ≤ ∑ i, (c i).size := by
      calc
        k = ∑ _i : Fin k, 1 := by simp
        _ ≤ _ := sum_le_sum (fun i _ => (c i).size_pos)
    have hk : k ≤ m := by omega
    have hkreal : (k : ℝ) ≤ m := by exact_mod_cast hk
    let A : ℝ := 2 * ((m : ℝ) + 1) ^ 2
    let R := s * (Nat.log 2 m + 3)
    let D := univ.sup (fun i => (c i).depth)
    let E := (2 * R + 2) ^ D
    let V := A ^ E
    have hA : 2 ≤ A := by dsimp [A]; nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hA1 : 1 ≤ A := by linarith
    have hV : 1 ≤ V := one_le_pow₀ hA1
    have hE : 1 ≤ E := by dsimp [E]; exact Nat.one_le_pow D (2 * R + 2) (by omega)
    have hchildren (i : Fin k) : (c i).sampleNormBound s ≤ V := by
      have hdepth := le_sup (f := fun j => (c j).depth) (mem_univ i)
      exact (ih i m (hsize i)).trans (pow_le_pow_right₀ hA1
        (Nat.pow_le_pow_right (by omega : 0 < 2 * R + 2) hdepth))
    have hsum : ∑ i, (c i).sampleNormBound s ≤ (m : ℝ) * V := by
      calc
        _ ≤ ∑ _i : Fin k, V := sum_le_sum (fun i _ => hchildren i)
        _ = (k : ℝ) * V := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hkreal (by linarith)
    have hS0 : 0 ≤ ∑ i, (c i).sampleNormBound s :=
      sum_nonneg (fun i _ => sampleNormBound_nonneg s (c i))
    have hbase : 1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s) ≤ A * V := by
      have hh := mul_le_mul hkreal (add_le_add (le_refl (2 : ℝ)) hsum)
        (by linarith : (0 : ℝ) ≤ 2 + ∑ i, (c i).sampleNormBound s) (Nat.cast_nonneg m)
      have hpoly := mul_le_mul_of_nonneg_left hV
        (show 0 ≤ (m : ℝ) ^ 2 + 4 * m + 2 by positivity)
      dsimp [A]
      nlinarith
    have hnonneg : 0 ≤ 1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s) := by
      positivity
    have hR : s * (Nat.log 2 k + 3) ≤ R :=
      Nat.mul_le_mul_left s (Nat.add_le_add_right (Nat.log_mono_right hk) 3)
    have hpow : (1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s)) ^
        (s * (Nat.log 2 k + 3)) ≤ (A * V) ^ R :=
      (pow_le_pow_left₀ hnonneg hbase _).trans
        (pow_le_pow_right₀ (by nlinarith) hR)
    have heq : (A * V) ^ R = A ^ ((E + 1) * R) := by
      dsimp only [V]
      rw [← pow_succ', ← pow_mul]
    have hplus : 1 + A ^ ((E + 1) * R) ≤ A ^ ((E + 1) * R + 1) := by
      have hz : 1 ≤ A ^ ((E + 1) * R) := one_le_pow₀ hA1
      rw [pow_succ]
      nlinarith
    have hexponent : (E + 1) * R + 1 ≤ (2 * R + 2) ^ (D + 1) := by
      have hRE : R ≤ R * E := by simpa using Nat.mul_le_mul_left R hE
      rw [pow_succ]
      change (E + 1) * R + 1 ≤ E * (2 * R + 2)
      nlinarith
    change 1 + (1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s)) ^
      (s * (Nat.log 2 k + 3)) ≤ A ^ ((2 * R + 2) ^ (1 + D))
    calc
      _ ≤ 1 + (A * V) ^ R := add_le_add (le_refl (1 : ℝ)) hpow
      _ = 1 + A ^ ((E + 1) * R) := by rw [heq]
      _ ≤ A ^ ((E + 1) * R + 1) := hplus
      _ ≤ _ := pow_le_pow_right₀ hA1 (by simpa [Nat.add_comm] using hexponent)

end TwoPointCorrelations.AC0Circuit

end OAI
