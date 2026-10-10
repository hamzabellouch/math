import OAI.Combinatorics.EditApproximation.Binary.UnreducedRational
import OAI.Combinatorics.EditApproximation.Numerics.Numerics
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The numerical primitives executed on unreduced fractions. Their exact
values agree with the rational routines; their stored denominators
have polynomial bit length without cancellation or Euclidean normalization. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

def one : UnreducedRational := ofRat 1



def sub (a b : UnreducedRational) : UnreducedRational := a.add b.neg

def pow (a : UnreducedRational) : ℕ → UnreducedRational
  | 0 => one
  | n + 1 => (pow a n).mul a

@[simp] theorem value_one : one.value = 1 := value_ofRat _
@[simp] theorem value_nat (n : ℕ) : (nat n).value = n := by simp [nat, value]
@[simp] theorem value_sub (a b : UnreducedRational) : (a.sub b).value = a.value - b.value := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem value_pow (a : UnreducedRational) (n : ℕ) : (a.pow n).value = a.value ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

theorem pow_den (a : UnreducedRational) (n : ℕ) : (a.pow n).den = a.den ^ n := by
  induction n with
  | zero => simp [pow, one, ofRat]
  | succ n ih => simp [pow, mul, ih, pow_succ]

theorem pow_den_bits (a : UnreducedRational) (n : ℕ) :
    Nat.size (a.pow n).den ≤ n * Nat.size a.den + 1 := by
  rw [pow_den]
  exact natural_power_bit_length _ _

theorem nat_inv_den (n : ℕ) (hn : 0 < n) : (nat n).inv.den = n := by
  simp [nat, inv, hn.ne']

def logarithmPartial (b : UnreducedRational) : ℕ → UnreducedRational
  | 0 => zero
  | K + 1 => (logarithmPartial b K).add ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))

def logarithm (r : UnreducedRational) (K : ℕ) : UnreducedRational :=
  (nat 2).mul (logarithmPartial ((r.sub one).div (r.add one)) K)

theorem logarithmPartial_value (b : UnreducedRational) (K : ℕ) :
    (logarithmPartial b K).value =
      ∑ k ∈ range K, b.value ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
  induction K with
  | zero => simp [logarithmPartial]
  | succ K ih => simp [logarithmPartial, ih, sum_range_succ]

@[simp] theorem logarithm_value (r : UnreducedRational) (K : ℕ) :
    (logarithm r K).value = rationalLogApproximation r.value K := by
  simp [logarithm, logarithmPartial_value, rationalLogApproximation]

theorem logarithmPartial_den_bits (b : UnreducedRational) (K : ℕ) :
    Nat.size (logarithmPartial b K).den ≤
      K * K * Nat.size b.den + K * (Nat.size (2 * K + 1) + 1) + 1 := by
  induction K with
  | zero => simp [logarithmPartial, zero]
  | succ K ih =>
    have hp := pow_den_bits b (2 * K + 1)
    have ht := mul_den_bits (b.pow (2 * K + 1)) (nat (2 * K + 1)).inv
    rw [nat_inv_den _ (by omega)] at ht
    have ha := add_den_bits (logarithmPartial b K)
      ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))
    have hs := Nat.size_le_size (by omega : 2 * K + 1 ≤ 2 * (K + 1) + 1)
    change Nat.size ((logarithmPartial b K).add
      ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))).den ≤ _
    change Nat.size ((b.pow (2 * K + 1)).div (nat (2 * K + 1))).den ≤ _ at ht
    have hweighted := Nat.mul_le_mul_left K hs
    nlinarith only [ih, hp, ht, ha, hweighted, hs]

theorem logarithm_storageBits (r : UnreducedRational) (K : ℕ) (hr : 0 ≤ r.value) :
    (logarithm r K).storageBits ≤ Nat.size (2 * K) +
      2 * (K * K * Nat.size ((r.sub one).div (r.add one)).den +
        K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  apply storageBits_le
  · rw [logarithm_value]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using rationalLogApproximation_abs_bound r.value K hr
  · simpa only [logarithm, mul, nat, Nat.one_mul] using
      logarithmPartial_den_bits ((r.sub one).div (r.add one)) K

def optimizerStep (j : ℕ) : UnreducedRational := (nat 2).div (nat (j + 2))

def optimizerIterate {ι : Type*} (initial : ι → UnreducedRational)
    (selected : ℕ → ι → UnreducedRational) : ℕ → ι → UnreducedRational
  | 0 => initial
  | j + 1 => fun i => ((one.sub (optimizerStep j)).mul (optimizerIterate initial selected j i)).add
      ((optimizerStep j).mul (selected j i))

@[simp] theorem optimizerStep_value (j : ℕ) :
    (optimizerStep j).value = 2 / ((j : ℚ) + 2) := by
  simp [optimizerStep]

theorem optimizerIterate_value {ι : Type*} (initial : ι → UnreducedRational)
    (selected : ℕ → ι → UnreducedRational) (K : ℕ) (i : ι) :
    (optimizerIterate initial selected K i).value =
      rationalOptimizerIterate (fun i => (initial i).value) (fun j i => (selected j i).value) K i := by
  induction K with
  | zero => rfl
  | succ K ih => simp [optimizerIterate, rationalOptimizerIterate, ih]

theorem optimizerStep_den (j : ℕ) : (optimizerStep j).den = j + 2 := by
  change (nat 2).den * (nat (j + 2)).inv.den = j + 2
  rw [nat_inv_den _ (by omega)]
  simp [nat]

theorem optimizerIterate_den_bits {ι : Type*} (initial : ι → UnreducedRational)
    (selected : ℕ → ι → UnreducedRational) (K B : ℕ) (i : ι)
    (hinitial : Nat.size (initial i).den ≤ B)
    (hselected : ∀ j < K, Nat.size (selected j i).den ≤ B) :
    Nat.size (optimizerIterate initial selected K i).den ≤
      B + K * (2 * Nat.size (K + 1) + B) := by
  induction K with
  | zero => simpa [optimizerIterate] using hinitial
  | succ K ih =>
    have hp := ih (fun j hj => hselected j (by omega))
    have hs := hselected K (by omega)
    have hsize := Nat.size_le_size (by omega : K + 1 ≤ K + 1 + 1)
    have hfirst := mul_den_bits (one.sub (optimizerStep K)) (optimizerIterate initial selected K i)
    have hsecond := mul_den_bits (optimizerStep K) (selected K i)
    have hsum := add_den_bits
      ((one.sub (optimizerStep K)).mul (optimizerIterate initial selected K i))
      ((optimizerStep K).mul (selected K i))
    have hcomplement : (one.sub (optimizerStep K)).den = K + 2 := by
      simp only [sub, add, neg, one, ofRat, Rat.den_one, Nat.one_mul, optimizerStep_den]
    rw [hcomplement] at hfirst
    rw [optimizerStep_den] at hsecond
    change Nat.size (((one.sub (optimizerStep K)).mul (optimizerIterate initial selected K i)).add
      ((optimizerStep K).mul (selected K i))).den ≤ _
    have hweighted := Nat.mul_le_mul_left K hsize
    nlinarith only [hp, hs, hfirst, hsecond, hsum, hweighted]

end UnreducedRational
end EditApproximation

end OAI
