import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI


open scoped BigOperators Polynomial

noncomputable section

namespace InternalCatalan

open Polynomial

def oddPrimeWeight (p : ℕ) : (ZMod p)[X] := (1 - X ^ 2) ^ ((p - 1) / 2)

private theorem one_sub_X_sq_pow_expansion (R : Type*) [CommRing R] (s : ℕ) :
    (1 - X ^ 2 : R[X]) ^ s =
      ∑ k ∈ Finset.range (s + 1),
        C ((-1 : R) ^ k * (s.choose k : R)) * X ^ (2 * k) := by
  calc
    (1 - X ^ 2 : R[X]) ^ s = (-X ^ 2 + 1) ^ s := by congr 1; ring
    _ = ∑ k ∈ Finset.range (s + 1),
        (-X ^ 2 : R[X]) ^ k * 1 ^ (s - k) * (s.choose k : R[X]) :=
      add_pow (-X ^ 2 : R[X]) 1 s
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [neg_pow, ← pow_mul]
      simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, C_eq_natCast]
      ring

private theorem one_sub_X_sq_pow_coeff_even (R : Type*) [CommRing R] (s k : ℕ) :
    ((1 - X ^ 2 : R[X]) ^ s).coeff (2 * k) = (-1 : R) ^ k * (s.choose k : R) := by
  rw [one_sub_X_sq_pow_expansion, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    have hne : 2 * k ≠ 2 * j := by omega
    simp [hne]
  · intro hk
    have hsk : s < k := by
      simp only [Finset.mem_range] at hk
      omega
    simp [Nat.choose_eq_zero_of_lt hsk]

private theorem one_sub_X_sq_pow_coeff_odd (R : Type*) [CommRing R] (s d : ℕ)
    (hd : d % 2 ≠ 0) : ((1 - X ^ 2 : R[X]) ^ s).coeff d = 0 := by
  rw [one_sub_X_sq_pow_expansion, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [coeff_C_mul_X_pow]
  have hne : d ≠ 2 * k := by omega
  simp [hne]

theorem oddPrimeWeight_coeff_even (p k : ℕ) :
    (oddPrimeWeight p).coeff (2 * k) =
      (-1 : ZMod p) ^ k * (((p - 1) / 2).choose k : ZMod p) :=
  one_sub_X_sq_pow_coeff_even (ZMod p) ((p - 1) / 2) k

theorem oddPrimeWeight_coeff_odd (p d : ℕ) (hd : d % 2 ≠ 0) :
    (oddPrimeWeight p).coeff d = 0 :=
  one_sub_X_sq_pow_coeff_odd (ZMod p) ((p - 1) / 2) d hd

theorem oddPrimeWeight_coeff_eq_zero_of_ge {p d : ℕ} (hp : 0 < p) (hd : p ≤ d) :
    (oddPrimeWeight p).coeff d = 0 := by
  by_cases he : d % 2 = 0
  · have heq : d = 2 * (d / 2) := by omega
    rw [heq, oddPrimeWeight_coeff_even]
    have hlt : (p - 1) / 2 < d / 2 := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  · exact oddPrimeWeight_coeff_odd p d he

private theorem one_sub_X_sq_pow_coeff_reverse (R : Type*) [CommRing R] (s d : ℕ)
    (hd : d ≤ 2 * s) :
    ((1 - X ^ 2 : R[X]) ^ s).coeff (2 * s - d) =
      (-1 : R) ^ s * ((1 - X ^ 2 : R[X]) ^ s).coeff d := by
  by_cases he : d % 2 = 0
  · have hd2 : d = 2 * (d / 2) := by omega
    generalize d / 2 = k at hd2
    subst d
    have hk : k ≤ s := by omega
    have hr : 2 * s - 2 * k = 2 * (s - k) := by omega
    rw [hr, one_sub_X_sq_pow_coeff_even, one_sub_X_sq_pow_coeff_even,
      Nat.choose_symm hk]
    have hprod : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
      rw [← mul_pow]
      simp
    have hsign : (-1 : R) ^ (s - k) = (-1 : R) ^ s * (-1 : R) ^ k := by
      calc
        (-1 : R) ^ (s - k) =
            (-1 : R) ^ (s - k) * ((-1 : R) ^ k * (-1 : R) ^ k) := by
          rw [hprod, mul_one]
        _ = ((-1 : R) ^ (s - k) * (-1 : R) ^ k) * (-1 : R) ^ k := by ring
        _ = (-1 : R) ^ s * (-1 : R) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
    rw [hsign]
    ring
  · have hr : (2 * s - d) % 2 ≠ 0 := by omega
    rw [one_sub_X_sq_pow_coeff_odd R s (2 * s - d) hr,
      one_sub_X_sq_pow_coeff_odd R s d he, mul_zero]

theorem oddPrimeWeight_coeff_reverse {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : d < p) :
    (oddPrimeWeight p).coeff (p - 1 - d) =
      (-1 : ZMod p) ^ ((p - 1) / 2) * (oddPrimeWeight p).coeff d := by
  have hodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hdeg : 2 * ((p - 1) / 2) = p - 1 := by omega
  simpa only [oddPrimeWeight, hdeg] using
    one_sub_X_sq_pow_coeff_reverse (ZMod p) ((p - 1) / 2) d (by omega)

theorem oddPrimeWeight_four_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (4 : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    rcases (Nat.dvd_prime Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz) with h | h
    · exact hp.ne_one h
    · exact hp2 h
  rw [show (4 : ZMod p) = (2 : ZMod p) * 2 by norm_num]
  exact mul_ne_zero htwo htwo

theorem oddPrimeWeight_four_pow_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k : ℕ) : (4 : ZMod p) ^ k ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  exact pow_ne_zero _ (oddPrimeWeight_four_ne_zero hp hp2)

theorem oddPrimeWeight_centralCoeff_mul_identity {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 * k < p) :
    (-1 : ZMod p) ^ k * (((p - 1) / 2).choose k : ZMod p) * 4 ^ k =
      (Nat.centralBinom k : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  let m : ℕ := (p - 1) / 2
  have hm : 2 * m + 1 = p := by
    have hodd := hp.eq_two_or_odd.resolve_left hp2
    have hpos := hp.two_le
    dsimp [m]
    omega
  have hmcast : 2 * (m : ZMod p) + 1 = 0 := by
    have hh := congrArg (fun a : ℕ ↦ (a : ZMod p)) hm
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      ZMod.natCast_self] using hh
  change (-1 : ZMod p) ^ k * (m.choose k : ZMod p) * 4 ^ k = _
  revert hk
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    have hkm : k ≤ m := by omega
    have hkprev : 2 * k < p := by omega
    have hknz : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro hz
      have hdiv := (ZMod.natCast_eq_zero_iff (k + 1) p).mp hz
      have hle := Nat.le_of_dvd (by omega : 0 < k + 1) hdiv
      omega
    have hchoose :
        (m.choose (k + 1) : ZMod p) * ((k : ZMod p) + 1) =
          (m.choose k : ZMod p) * ((m : ZMod p) - k) := by
      have hh := congrArg (fun a : ℕ ↦ (a : ZMod p))
        (Nat.choose_succ_right_eq m k)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hkm] using hh
    have hcentral :
        (((k + 1 : ℕ) : ZMod p)) * (Nat.centralBinom (k + 1) : ZMod p) =
          2 * (2 * (k : ZMod p) + 1) * (Nat.centralBinom k : ZMod p) := by
      have hh := congrArg (fun a : ℕ ↦ (a : ZMod p))
        (Nat.succ_mul_centralBinom_succ k)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hh
    have hfactor : (-4 : ZMod p) * ((m : ZMod p) - k) =
        2 * (2 * (k : ZMod p) + 1) := by
      linear_combination -2 * hmcast
    apply mul_left_cancel₀ hknz
    calc
      (((k + 1 : ℕ) : ZMod p)) *
          ((-1 : ZMod p) ^ (k + 1) * (m.choose (k + 1) : ZMod p) * 4 ^ (k + 1)) =
          (-1 : ZMod p) ^ k * 4 ^ k * (-4) *
            ((m.choose (k + 1) : ZMod p) * ((k : ZMod p) + 1)) := by
              simp only [Nat.cast_add, Nat.cast_one, pow_succ]
              ring
      _ = (-1 : ZMod p) ^ k * 4 ^ k * (-4) *
          ((m.choose k : ZMod p) * ((m : ZMod p) - k)) := by rw [hchoose]
      _ = ((-4 : ZMod p) * ((m : ZMod p) - k)) *
          ((-1 : ZMod p) ^ k * (m.choose k : ZMod p) * 4 ^ k) := by ring
      _ = 2 * (2 * (k : ZMod p) + 1) * (Nat.centralBinom k : ZMod p) := by
        rw [hfactor, ih hkprev]
      _ = (((k + 1 : ℕ) : ZMod p)) * (Nat.centralBinom (k + 1) : ZMod p) :=
        hcentral.symm

theorem oddPrimeWeight_centralCoeff_identity {p k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 2 * k < p) :
    (-1 : ZMod p) ^ k * (((p - 1) / 2).choose k : ZMod p) =
      ((2 * k).choose k : ZMod p) / (4 : ZMod p) ^ k := by
  apply (eq_div_iff (oddPrimeWeight_four_pow_ne_zero hp.out hp2 k)).2
  exact oddPrimeWeight_centralCoeff_mul_identity hp.out hp2 hk

theorem oddPrimeWeight_four_pow_isUnit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k : ℕ) : IsUnit ((4 : ZMod p) ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  exact isUnit_iff_ne_zero.mpr (oddPrimeWeight_four_pow_ne_zero hp hp2 k)

theorem oddPrimeWeight_coeff_central {p k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 2 * k < p) :
    (oddPrimeWeight p).coeff (2 * k) =
      ((2 * k).choose k : ZMod p) / (4 : ZMod p) ^ k := by
  rw [oddPrimeWeight_coeff_even]
  exact oddPrimeWeight_centralCoeff_identity hp2 hk

theorem oddPrimeWeight_coeff_of_lt {p d : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hd : d < p) :
    (oddPrimeWeight p).coeff d =
      if d % 2 = 0 then (d.choose (d / 2) : ZMod p) / (4 : ZMod p) ^ (d / 2) else 0 := by
  by_cases he : d % 2 = 0
  · rw [ite_eq_left he]
    have heq : 2 * (d / 2) = d := by omega
    simpa only [heq] using
      oddPrimeWeight_coeff_central hp2 (show 2 * (d / 2) < p by omega)
  · rw [ite_eq_right he]
    exact oddPrimeWeight_coeff_odd p d he

end InternalCatalan

end

end OAI
