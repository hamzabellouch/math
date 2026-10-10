import OAI.Combinatorics.EditApproximation.Binary.UnreducedOptimizer

namespace OAI

/-! Polynomial raw storage bounds used by the Boolean numerical loops. -/

namespace EditApproximation
namespace UnreducedRational

open Finset

theorem storageBits_nat (n : ℕ) : (nat n).storageBits = Nat.size n + 2 := by
  simp [nat, storageBits]

theorem storageBits_one : one.storageBits = 3 := by decide

theorem storageBits_zero : zero.storageBits = 2 := by decide

theorem storageBits_neg (a : UnreducedRational) : a.neg.storageBits = a.storageBits := by
  simp [neg, storageBits]

theorem storageBits_add (a b : UnreducedRational) :
    (a.add b).storageBits ≤ 2 * a.storageBits + 2 * b.storageBits + 2 := by
  have hnum := (Nat.size_le_size (Int.natAbs_add_le (a.num * b.den) (b.num * a.den))).trans
    (natural_sum_bit_length (a.num * b.den).natAbs (b.num * a.den).natAbs)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnum
  have hleft := natural_product_bit_length a.num.natAbs b.den
  have hright := natural_product_bit_length b.num.natAbs a.den
  have hden := add_den_bits a b
  dsimp only [add, storageBits] at *
  omega

theorem storageBits_mul (a b : UnreducedRational) :
    (a.mul b).storageBits ≤ a.storageBits + b.storageBits := by
  have hnum := natural_product_bit_length a.num.natAbs b.num.natAbs
  have hden := mul_den_bits a b
  simp only [mul, storageBits, Int.natAbs_mul] at *
  omega

theorem storageBits_sub (a b : UnreducedRational) :
    (a.sub b).storageBits ≤ 2 * a.storageBits + 2 * b.storageBits + 2 := by
  simpa only [sub, storageBits_neg] using storageBits_add a b.neg

theorem storageBits_inv (a : UnreducedRational) : a.inv.storageBits ≤ a.storageBits + 2 := by
  by_cases h : a.num = 0
  · simp only [inv, h, ↓reduceDIte, storageBits_zero]
    omega
  · simp only [inv, h, ↓reduceDIte, storageBits, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero h, Int.natAbs_natCast, Nat.one_mul]
    omega

theorem storageBits_div (a b : UnreducedRational) :
    (a.div b).storageBits ≤ a.storageBits + b.storageBits + 2 := by
  exact (storageBits_mul a b.inv).trans (by have h := storageBits_inv b; omega)

theorem logarithmRatio_storageBits (r : UnreducedRational) :
    ((r.sub one).div (r.add one)).storageBits ≤ 4 * r.storageBits + 18 := by
  have hsub := storageBits_sub r one
  have hadd := storageBits_add r one
  have hdiv := storageBits_div (r.sub one) (r.add one)
  rw [storageBits_one] at hsub hadd
  omega

theorem logarithm_storageBits_poly (r : UnreducedRational) (K : ℕ) (hr : 0 ≤ r.value) :
    (logarithm r K).storageBits ≤
      Nat.size (2 * K) + 2 * (K * K * (4 * r.storageBits + 18) +
        K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  have h := logarithm_storageBits r K hr
  have hratio := logarithmRatio_storageBits r
  have hd : Nat.size ((r.sub one).div (r.add one)).den ≤ 4 * r.storageBits + 18 := by
    exact (by dsimp only [storageBits]; omega :
      Nat.size ((r.sub one).div (r.add one)).den ≤ ((r.sub one).div (r.add one)).storageBits).trans hratio
  have hm := Nat.mul_le_mul_left (K * K) hd
  omega

theorem logarithmPartial_abs_le (b : UnreducedRational) (K : ℕ) (hb : |b.value| ≤ 1) :
    |(logarithmPartial b K).value| ≤ K := by
  rw [logarithmPartial_value]
  calc
    _ ≤ ∑ k ∈ range K, |b.value ^ (2 * k + 1) / (2 * k + 1 : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ range K, (1 : ℚ) := by
      apply sum_le_sum
      intro k _
      have hd : (0 : ℚ) < (2 * k + 1 : ℕ) := by positivity
      have hd1 : (1 : ℚ) ≤ (2 * k + 1 : ℕ) := by norm_cast; omega
      rw [abs_div, abs_pow, abs_of_pos hd]
      exact (div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hb) hd.le).trans
        ((div_le_one₀ hd).mpr hd1)
    _ = K := by simp

theorem logarithmPartial_storageBits (b : UnreducedRational) (K : ℕ) (hb : |b.value| ≤ 1) :
    (logarithmPartial b K).storageBits ≤ Nat.size K +
      2 * (K * K * Nat.size b.den + K * (Nat.size (2 * K + 1) + 1) + 1) + 1 :=
  storageBits_le _ K _ (logarithmPartial_abs_le b K hb) (logarithmPartial_den_bits b K)

theorem pow_storageBits_abs_le_one (b : UnreducedRational) (K : ℕ) (hb : |b.value| ≤ 1) :
    (b.pow K).storageBits ≤ 2 * (K * Nat.size b.den + 1) + 2 := by
  have hv : |(b.pow K).value| ≤ (1 : ℕ) := by
    rw [value_pow, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hb
  have h := storageBits_le (b.pow K) 1 _ hv (pow_den_bits b K)
  simp only [Nat.size_one] at h
  omega

theorem pow_storageBits (a : UnreducedRational) (n : ℕ) :
    (a.pow n).storageBits ≤ 3 + n * a.storageBits := by
  induction n with
  | zero => simpa only [pow, Nat.zero_mul, Nat.add_zero] using storageBits_one.le
  | succ n ih =>
    have hm := storageBits_mul (a.pow n) a
    simp only [pow]
    nlinarith only [ih, hm]

def logarithmStorageBudget (B K : ℕ) : ℕ :=
  Nat.size (2 * K) + 2 * (K * K * (4 * B + 18) +
    K * (Nat.size (2 * K + 1) + 1) + 1) + 1

theorem logarithmStorageBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmStorageBudget A K ≤ logarithmStorageBudget B K := by
  have hm := Nat.mul_le_mul_left (K * K) (show 4 * A + 18 ≤ 4 * B + 18 by omega)
  unfold logarithmStorageBudget
  omega

def gradientStorageBudget (G pointBits linearBits : ℕ) : ℕ :=
  4 * logarithmStorageBudget (2 * pointBits + 2 * (5 + 50 * (Nat.size G + 2)) + 2) (G ^ 60) +
    2 * linearBits + 18

theorem gradientCell_storageBits {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d)
    (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
    (gradientCell G linear point i).storageBits ≤
      gradientStorageBudget G (point.get i).storageBits (linear.get i).storageBits := by
  let smoothing := (nat G).pow 50
  let shifted := (point.get i).add smoothing.inv
  have hs : smoothing.storageBits ≤ 3 + 50 * (Nat.size G + 2) := by
    simpa only [smoothing, storageBits_nat] using pow_storageBits (nat G) 50
  have hi := storageBits_inv smoothing
  have ha := storageBits_add (point.get i) smoothing.inv
  have hshift : shifted.storageBits ≤ 2 * (point.get i).storageBits +
      2 * (5 + 50 * (Nat.size G + 2)) + 2 := by
    dsimp only [shifted]
    omega
  have hpositive : 0 ≤ shifted.value := by
    dsimp only [shifted, smoothing]
    simp only [value_add, value_inv, value_pow, value_nat]
    exact add_nonneg hpoint (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg G) _))
  have hlog := (logarithm_storageBits_poly shifted (G ^ 60) hpositive).trans
    (logarithmStorageBudget_mono hshift (G ^ 60))
  have hsub := storageBits_sub (logarithm shifted (G ^ 60)).neg one
  rw [storageBits_neg, storageBits_one] at hsub
  have hadd := storageBits_add ((logarithm shifted (G ^ 60)).neg.sub one) (linear.get i)
  change (((logarithm shifted (G ^ 60)).neg.sub one).add (linear.get i)).storageBits ≤ _
  unfold gradientStorageBudget
  omega

theorem dotList_den_bits {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (L R : ℕ)
    (hl : ∀ i ∈ indices, Nat.size (left.get i).den ≤ L)
    (hr : ∀ i ∈ indices, Nat.size (right.get i).den ≤ R) :
    Nat.size (dotList left right indices).den ≤ 1 + indices.length * (L + R) := by
  induction indices with
  | nil => simp [dotList, zero]
  | cons i rest ih =>
    have ht := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => hr i (List.mem_cons_of_mem _ hi))
    have hi := mul_den_bits (left.get i) (right.get i)
    have hs := add_den_bits ((left.get i).mul (right.get i)) (dotList left right rest)
    have hil := hl i List.mem_cons_self
    have hir := hr i List.mem_cons_self
    change Nat.size (((left.get i).mul (right.get i)).add (dotList left right rest)).den ≤ _
    simp only [List.length_cons]
    nlinarith only [ht, hi, hs, hil, hir]

theorem dotList_abs_le {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (L R : ℕ)
    (hl : ∀ i ∈ indices, |(left.get i).value| ≤ L)
    (hr : ∀ i ∈ indices, |(right.get i).value| ≤ R) :
    |(dotList left right indices).value| ≤ indices.length * L * R := by
  induction indices with
  | nil => simp [dotList]
  | cons i rest ih =>
    have ht := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => hr i (List.mem_cons_of_mem _ hi))
    have hi := mul_le_mul (hl i List.mem_cons_self) (hr i List.mem_cons_self)
      (abs_nonneg _) (Nat.cast_nonneg L)
    simp only [dotList, value_add, value_mul]
    calc
      _ ≤ |(left.get i).value * (right.get i).value| + |(dotList left right rest).value| := abs_add_le _ _
      _ ≤ (L : ℚ) * R + rest.length * L * R := by rw [abs_mul]; exact add_le_add hi ht
      _ = (i :: rest).length * L * R := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem dotList_storageBits {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (BL BR VL VR : ℕ)
    (hlbits : ∀ i ∈ indices, Nat.size (left.get i).den ≤ BL)
    (hrbits : ∀ i ∈ indices, Nat.size (right.get i).den ≤ BR)
    (hlvalue : ∀ i ∈ indices, |(left.get i).value| ≤ VL)
    (hrvalue : ∀ i ∈ indices, |(right.get i).value| ≤ VR) :
    (dotList left right indices).storageBits ≤ Nat.size (indices.length * VL * VR) +
      2 * (1 + indices.length * (BL + BR)) + 1 := by
  apply storageBits_le
  · simpa only [Nat.cast_mul] using dotList_abs_le left right indices VL VR hlvalue hrvalue
  · exact dotList_den_bits left right indices BL BR hlbits hrbits

theorem logarithmPartial_storageBits_uniform (b : UnreducedRational) (j K : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    (logarithmPartial b j).storageBits ≤ Nat.size K +
      2 * (K * K * Nat.size b.den + K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  have h := logarithmPartial_storageBits b j hb
  have hs := Nat.size_le_size hj
  have hsodd := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  have hquad := Nat.mul_le_mul_right (Nat.size b.den) (Nat.mul_le_mul hj hj)
  have hlinear := Nat.mul_le_mul hj (Nat.add_le_add_right hsodd 1)
  omega

end UnreducedRational
end EditApproximation

end OAI
