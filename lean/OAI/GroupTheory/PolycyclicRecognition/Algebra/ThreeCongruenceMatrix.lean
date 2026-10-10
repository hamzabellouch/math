import OAI.GroupTheory.PolycyclicRecognition.Algebra.ThreePrimitiveIntegerFamily
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SquareZeroPower
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

namespace OAI

/-! # Integral matrices congruent to the identity modulo three -/
noncomputable section
namespace PolycyclicRecognition
open Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

def matrixMod (m : ℕ) : Matrix I I ℤ →+* Matrix I I (ZMod m) :=
  (Int.castRingHom (ZMod m)).mapMatrix

@[simp] theorem matrixMod_apply (m : ℕ) (A : Matrix I I ℤ) (i j : I) :
    matrixMod m A i j = (A i j : ZMod m) := rfl

theorem matrixMod_zsmul (m : ℕ) (a : ℤ) (A : Matrix I I ℤ) :
    matrixMod m (a • A) = (a : ZMod m) • matrixMod m A := by
  ext i j
  change ((a * A i j : ℤ) : ZMod m) = (a : ZMod m) * (A i j : ZMod m)
  exact Int.cast_mul a (A i j)

theorem zmod_three_power_zero (a b : ℕ) (h : a ≤ b) :
    (3 : ZMod (3 ^ a)) ^ b = 0 := by
  have hd : 3 ^ a ∣ (3 : ℕ) ^ b := pow_dvd_pow 3 h
  have hz := (ZMod.natCast_eq_zero_iff (3 ^ b) (3 ^ a)).mpr hd
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz

theorem integerMatrix_three_primitive (A : Matrix I I ℤ)
    (hne : A ≠ 1) (h3 : ∀ i j, (3 : ℤ) ∣ (A - 1) i j) :
    ∃ k : ℕ, 0 < k ∧ ∃ C : Matrix I I ℤ,
      A = 1 + (3 ^ k : ℤ) • C ∧ ∃ i j, ¬(3 : ℤ) ∣ C i j := by
  have hnon : ∃ p : I × I, (A - 1) p.1 p.2 ≠ 0 := by
    by_contra h
    apply hne
    have hz : A - 1 = 0 := by
      ext i j
      exact not_not.mp (fun hij => h ⟨(i, j), hij⟩)
    exact sub_eq_zero.mp hz
  obtain ⟨k, hk, c, hc, p, hp⟩ :=
    integerFamily_three_primitive (fun p : I × I => (A - 1) p.1 p.2) hnon
      (fun p => h3 p.1 p.2)
  let C : Matrix I I ℤ := fun i j => c (i, j)
  refine ⟨k, hk, C, ?_, p.1, p.2, hp⟩
  have he : A - 1 = (3 ^ k : ℤ) • C := by
    ext i j
    exact hc (i, j)
  simpa only [add_comm] using sub_eq_iff_eq_add.mp he

theorem integerMatrix_prime_three_dvd (A C : Matrix I I ℤ) (k p : ℕ)
    (hk : 0 < k) (hA : A = 1 + (3 ^ k : ℤ) • C) (hpow : A ^ p = 1) :
    ∀ i j, (3 : ℤ) ∣ (p : ℤ) * C i j := by
  let m := 3 ^ (k + 1)
  let D := matrixMod (I := I) m C
  let s : ZMod m := 3 ^ k
  let X : Matrix I I (ZMod m) := s • D
  have hX : X * X = 0 := by
    change (s • D) * (s • D) = 0
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hs : s * s = 0 := by
      change (3 : ZMod (3 ^ (k + 1))) ^ k * 3 ^ k = 0
      rw [← pow_add]
      exact zmod_three_power_zero (k + 1) (k + k) (by omega)
    rw [hs, zero_smul]
  have he : (1 + X) ^ p = 1 := by
    have hm := congrArg (matrixMod (I := I) m) hpow
    rw [map_pow, map_one, hA, map_add, map_one, matrixMod_zsmul] at hm
    simpa only [Int.cast_pow, Int.cast_ofNat] using hm
  rw [one_add_pow_of_square_zero X hX p] at he
  have hz : p • X = 0 := by simpa using he
  intro i j
  have hc : (((p : ℤ) * (3 ^ k * C i j) : ℤ) : ZMod m) = 0 := by
    have hij := congrArg (fun M : Matrix I I (ZMod m) => M i j) hz
    simpa [X, s, D, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul] using hij
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((p : ℤ) * (3 ^ k * C i j)) m).mp hc
  have heq : (p : ℤ) * (3 ^ k * C i j) = 3 ^ k * ((p : ℤ) * C i j) := by ring
  rw [heq] at hd
  have hd' : (3 ^ k : ℤ) * 3 ∣ 3 ^ k * ((p : ℤ) * C i j) := by
    simpa only [m, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, pow_succ] using hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero k (by norm_num : (3 : ℤ) ≠ 0))).mp hd'

theorem integerMatrix_cube_three_dvd (A C : Matrix I I ℤ) (k : ℕ)
    (hk : 0 < k) (hA : A = 1 + (3 ^ k : ℤ) • C) (hpow : A ^ 3 = 1) :
    ∀ i j, (3 : ℤ) ∣ C i j := by
  let m := 3 ^ (k + 2)
  let D := matrixMod (I := I) m C
  let s : ZMod m := 3 ^ k
  let X : Matrix I I (ZMod m) := s • D
  have hsq : X * X = (s * s) • (D * D) := by
    change (s • D) * (s • D) = _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hX2 : 3 • (X * X) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod m) 3, hsq, smul_smul]
    norm_num only [Nat.cast_ofNat]
    have hs : (3 : ZMod m) * (s * s) = 0 := by
      change (3 : ZMod (3 ^ (k + 2))) * (3 ^ k * 3 ^ k) = 0
      rw [← pow_add, ← pow_succ']
      exact zmod_three_power_zero (k + 2) (k + k + 1) (by omega)
    rw [hs, zero_smul]
  have hX3 : X * X * X = 0 := by
    rw [hsq]
    change ((s * s) • (D * D)) * (s • D) = 0
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hs : (s * s) * s = 0 := by
      change ((3 : ZMod (3 ^ (k + 2))) ^ k * 3 ^ k) * 3 ^ k = 0
      rw [← pow_add, ← pow_add]
      exact zmod_three_power_zero (k + 2) (k + k + k) (by omega)
    rw [hs, zero_smul]
  have he : (1 + X) ^ 3 = 1 := by
    have hm := congrArg (matrixMod (I := I) m) hpow
    rw [map_pow, map_one, hA, map_add, map_one, matrixMod_zsmul] at hm
    simpa only [Int.cast_pow, Int.cast_ofNat] using hm
  rw [one_add_cube X, hX2, hX3, add_zero, add_zero] at he
  have hz : 3 • X = 0 := by simpa using he
  intro i j
  have hc : (((3 : ℤ) * (3 ^ k * C i j) : ℤ) : ZMod m) = 0 := by
    have hij := congrArg (fun M : Matrix I I (ZMod m) => M i j) hz
    simpa [X, s, D, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul] using hij
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((3 : ℤ) * (3 ^ k * C i j)) m).mp hc
  have heq : (3 : ℤ) * (3 ^ k * C i j) = 3 ^ (k + 1) * C i j := by
    rw [pow_succ]
    ring
  rw [heq] at hd
  have hd' : (3 ^ (k + 1) : ℤ) * 3 ∣ 3 ^ (k + 1) * C i j := by
    simpa only [m, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, show k + 2 = (k + 1) + 1 by omega,
      pow_succ] using hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero (k + 1) (by norm_num : (3 : ℤ) ≠ 0))).mp hd'

theorem integerMatrix_eq_one_of_prime_order_three_congruence
    (A : Matrix I I ℤ) (p : ℕ) (hp : p.Prime) (hpow : A ^ p = 1)
    (h3 : ∀ i j, (3 : ℤ) ∣ (A - 1) i j) : A = 1 := by
  by_contra hne
  obtain ⟨k, hk, C, hA, i, j, hij⟩ := integerMatrix_three_primitive A hne h3
  have hdiv := integerMatrix_prime_three_dvd A C k p hk hA hpow i j
  have hpp : (3 : ℤ) ∣ (p : ℤ) := ((by norm_num : Prime (3 : ℤ)).dvd_mul.mp hdiv).resolve_right hij
  have hpn : 3 ∣ p := by exact_mod_cast hpp
  have hp3 : p = 3 := (hp.eq_one_or_self_of_dvd 3 hpn).resolve_left (by norm_num) |>.symm
  subst p
  exact hij (integerMatrix_cube_three_dvd A C k hk hA hpow i j)

end PolycyclicRecognition

end

end OAI
