import OAI.Combinatorics.EditApproximation.Binary.BinaryRawCost

namespace OAI

/-! Bit cost of the finite logarithm series on unreduced Boolean fractions.
Every bound is for the executed power/division/addition loops. -/

namespace EditApproximation
namespace BinaryFraction

def logarithmPartialWordBudget (b : BinaryFraction) (K : ℕ) : ℕ :=
  b.width +
    (Nat.size K + 2 * (K * K * Nat.size b.representation.den +
      K * (Nat.size (2 * K + 1) + 1) + 1) + 1) +
    (2 * ((2 * K + 1) * Nat.size b.representation.den + 1) + 2) +
    Nat.size (2 * K + 1) + 10

theorem logarithmPartialWordBudget_input (b : BinaryFraction) (K : ℕ) :
    b.width ≤ logarithmPartialWordBudget b K := by
  unfold logarithmPartialWordBudget
  omega

theorem logarithmPartialWordBudget_power (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ 2 * K + 1) (hb : |b.value| ≤ 1) :
    (b.powWithWork j).1.width ≤ logarithmPartialWordBudget b K := by
  have h := powWithWork_width_abs_le_one b j hb
  have hm := Nat.mul_le_mul_right (Nat.size b.representation.den) hj
  unfold logarithmPartialWordBudget
  omega

theorem logarithmPartialWordBudget_partial (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    (b.logarithmPartialWithWork j).1.width ≤ logarithmPartialWordBudget b K := by
  have hw := logarithmPartialWithWork_width_le_storageBits b j
  rw [logarithmPartialWithWork_representation] at hw
  have hs := UnreducedRational.logarithmPartial_storageBits_uniform b.representation j K hj hb
  unfold logarithmPartialWordBudget
  omega

theorem logarithmPartialWordBudget_nat (b : BinaryFraction) (K j : ℕ) (hj : j ≤ K) :
    (nat (2 * j + 1)).width ≤ logarithmPartialWordBudget b K := by
  have hw := nat_width_le_storageBits (2 * j + 1)
  rw [nat_representation, UnreducedRational.storageBits_nat] at hw
  have hs := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  unfold logarithmPartialWordBudget
  omega

theorem divWithWork_self_width (a b : BinaryFraction) :
    (a.divWithWork b).1.width ≤ (a.divWithWork b).1.representation.storageBits :=
  canonicalMulWithWork_self_width _ _

theorem logarithmPartialWordBudget_term (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).1.width ≤
      logarithmPartialWordBudget b K := by
  have hw := divWithWork_self_width (b.powWithWork (2 * j + 1)).1 (nat (2 * j + 1))
  rw [divWithWork_representation, powWithWork_representation, nat_representation] at hw
  have hs := UnreducedRational.storageBits_div (b.representation.pow (2 * j + 1))
    (UnreducedRational.nat (2 * j + 1))
  rw [UnreducedRational.storageBits_nat] at hs
  have hp := UnreducedRational.pow_storageBits_abs_le_one b.representation (2 * j + 1) hb
  have hm := Nat.mul_le_mul_right (Nat.size b.representation.den)
    (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  have hn := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
  unfold logarithmPartialWordBudget
  omega

def logarithmPartialBitStep (W K : ℕ) : ℕ :=
  (2 * K + 1) * (2000 * (W + 1) ^ 2 + 1) +
    2100 * (W + 2) ^ 2 + 6000 * (W + 1) ^ 2 + Nat.size (2 * K + 1) + 6

theorem logarithmPartialWithWork_cost_le (b : BinaryFraction) (K j : ℕ)
    (hj : j ≤ K) (hb : |b.value| ≤ 1) :
    (b.logarithmPartialWithWork j).2 ≤
      1 + j * logarithmPartialBitStep (logarithmPartialWordBudget b K) K := by
  induction j with
  | zero => simp [logarithmPartialWithWork]
  | succ j ih =>
    let W := logarithmPartialWordBudget b K
    have hp := ih (by omega)
    have hpower := powWithWork_cost_of_width b (2 * j + 1) W
      (logarithmPartialWordBudget_input b K) (by
        intro m hm
        exact logarithmPartialWordBudget_power b K m (by omega) hb)
    have hpower' : (b.powWithWork (2 * j + 1)).2 ≤
        1 + (2 * K + 1) * (2000 * (W + 1) ^ 2 + 1) := by
      have hm := Nat.mul_le_mul_right (2000 * (W + 1) ^ 2 + 1)
        (show 2 * j + 1 ≤ 2 * K + 1 by omega)
      omega
    have hdiv := divWithWork_cost (b.powWithWork (2 * j + 1)).1 (nat (2 * j + 1)) W
      (logarithmPartialWordBudget_power b K (2 * j + 1) (by omega) hb)
      (logarithmPartialWordBudget_nat b K j (by omega))
    have hadd := canonicalAddWithWork_cost (b.logarithmPartialWithWork j).1
      ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).1 W
      (logarithmPartialWordBudget_partial b K j (by omega) hb)
      (logarithmPartialWordBudget_term b K j (by omega) hb)
    have hn := Nat.size_le_size (show 2 * j + 1 ≤ 2 * K + 1 by omega)
    change (b.logarithmPartialWithWork j).2 + (b.powWithWork (2 * j + 1)).2 +
      ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).2 +
      (canonicalAddWithWork (b.logarithmPartialWithWork j).1
        ((b.powWithWork (2 * j + 1)).1.divWithWork (nat (2 * j + 1))).1).2 +
      Nat.size (2 * j + 1) + 5 ≤ _
    change (b.logarithmPartialWithWork j).2 ≤ 1 + j * logarithmPartialBitStep W K at hp
    change _ ≤ 1 + (j + 1) * logarithmPartialBitStep W K
    unfold logarithmPartialBitStep at hp ⊢
    nlinarith only [hp, hpower', hdiv, hadd, hn]

theorem logarithmPartialWithWork_cost (b : BinaryFraction) (K : ℕ) (hb : |b.value| ≤ 1) :
    (b.logarithmPartialWithWork K).2 ≤
      1 + K * logarithmPartialBitStep (logarithmPartialWordBudget b K) K :=
  logarithmPartialWithWork_cost_le b K K le_rfl hb

theorem logarithmRatio_abs_le_one (r : BinaryFraction) (hr : 0 ≤ r.value) :
    |((r.subWithWork one).1.divWithWork (canonicalAddWithWork r one).1).1.value| ≤ 1 := by
  rw [← representation_value, divWithWork_representation, subWithWork_representation,
    canonicalAddWithWork_representation, one_representation]
  simp only [UnreducedRational.value_div, UnreducedRational.value_sub,
    UnreducedRational.value_add, UnreducedRational.value_one, representation_value]
  have hd : 0 < r.value + 1 := by linarith
  rw [abs_div, abs_of_pos hd]
  exact (div_le_one₀ hd).mpr (abs_le.mpr ⟨by linarith, by linarith⟩)

def logarithmUniversalWordBudget (B K : ℕ) : ℕ :=
  B + (Nat.size K + 2 * (K * K * B + K * (Nat.size (2 * K + 1) + 1) + 1) + 1) +
    (2 * ((2 * K + 1) * B + 1) + 2) + Nat.size (2 * K + 1) + 10

theorem logarithmPartialWordBudget_le (b : BinaryFraction) (B K : ℕ) (hw : b.width ≤ B) :
    logarithmPartialWordBudget b K ≤ logarithmUniversalWordBudget B K := by
  have hd := (representation_den_bits_le_width b).trans hw
  have hquad := Nat.mul_le_mul_left (K * K) hd
  have hlin := Nat.mul_le_mul_left (2 * K + 1) hd
  unfold logarithmPartialWordBudget logarithmUniversalWordBudget
  omega

theorem logarithmPartialBitStep_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmPartialBitStep A K ≤ logarithmPartialBitStep B K := by
  have h1 := Nat.mul_self_le_mul_self (show A + 1 ≤ B + 1 by omega)
  have h2 := Nat.mul_self_le_mul_self (show A + 2 ≤ B + 2 by omega)
  simp only [← pow_two] at h1 h2
  have hm := Nat.mul_le_mul_left (2 * K + 1)
    (show 2000 * (A + 1) ^ 2 + 1 ≤ 2000 * (B + 1) ^ 2 + 1 by omega)
  unfold logarithmPartialBitStep
  omega

def logarithmRatio (r : BinaryFraction) : BinaryFraction :=
  ((r.subWithWork one).1.divWithWork (canonicalAddWithWork r one).1).1

theorem logarithmRatio_width (r : BinaryFraction) : (logarithmRatio r).width ≤ 8 * r.width + 22 := by
  have hw := divWithWork_self_width (r.subWithWork one).1 (canonicalAddWithWork r one).1
  rw [divWithWork_representation, subWithWork_representation, canonicalAddWithWork_representation,
    one_representation] at hw
  have hs := UnreducedRational.logarithmRatio_storageBits r.representation
  have hr := representation_storageBits_le r
  change (logarithmRatio r).width ≤ _ at hw
  omega

theorem one_width : one.width ≤ 3 := by decide

theorem sub_one_width (r : BinaryFraction) : (r.subWithWork one).1.width ≤ 4 * r.width + 10 := by
  have hw := canonicalAddWithWork_self_width r one.neg
  change (r.subWithWork one).1.width ≤ (r.subWithWork one).1.representation.storageBits at hw
  rw [subWithWork_representation, one_representation] at hw
  have hs := UnreducedRational.storageBits_sub r.representation UnreducedRational.one
  rw [UnreducedRational.storageBits_one] at hs
  have hr := representation_storageBits_le r
  omega

theorem add_one_width (r : BinaryFraction) : (canonicalAddWithWork r one).1.width ≤ 4 * r.width + 10 := by
  have hw := canonicalAddWithWork_width_le_storageBits r one
  rw [one_representation] at hw
  have hs := UnreducedRational.storageBits_add r.representation UnreducedRational.one
  rw [UnreducedRational.storageBits_one] at hs
  have hr := representation_storageBits_le r
  omega

def logarithmBitBudget (B K : ℕ) : ℕ :=
  let W := logarithmUniversalWordBudget (8 * B + 22) K
  12000 * (B + 4) ^ 2 + 2100 * (4 * B + 12) ^ 2 +
    K * logarithmPartialBitStep W K + 2000 * (W + 5) ^ 2 + 10

theorem logarithmWithWork_cost (r : BinaryFraction) (K : ℕ) (hr : 0 ≤ r.value) :
    (r.logarithmWithWork K).2 ≤ logarithmBitBudget r.width K := by
  let b := logarithmRatio r
  let W := logarithmUniversalWordBudget (8 * r.width + 22) K
  have hb : |b.value| ≤ 1 := logarithmRatio_abs_le_one r hr
  have hW : logarithmPartialWordBudget b K ≤ W :=
    logarithmPartialWordBudget_le b (8 * r.width + 22) K (logarithmRatio_width r)
  have hsub := subWithWork_cost r one (r.width + 3) (by omega) (by have h := one_width; omega)
  have hadd := canonicalAddWithWork_cost r one (r.width + 3) (by omega) (by have h := one_width; omega)
  have hdiv := divWithWork_cost (r.subWithWork one).1 (canonicalAddWithWork r one).1
    (4 * r.width + 10) (sub_one_width r) (add_one_width r)
  have hpartial := logarithmPartialWithWork_cost b K hb
  have hstep := Nat.mul_le_mul_left K (logarithmPartialBitStep_mono hW K)
  have hpartial' : (b.logarithmPartialWithWork K).2 ≤ 1 + K * logarithmPartialBitStep W K := by omega
  have hpwidth := (logarithmPartialWordBudget_partial b K K le_rfl hb).trans hW
  have htwo : (nat 2).width ≤ 4 := by decide
  have hmul := canonicalMulWithWork_cost (nat 2) (b.logarithmPartialWithWork K).1
    (W + 4) (by omega) (by omega)
  change (r.subWithWork one).2 + (canonicalAddWithWork r one).2 +
    ((r.subWithWork one).1.divWithWork (canonicalAddWithWork r one).1).2 +
    (b.logarithmPartialWithWork K).2 +
    (canonicalMulWithWork (nat 2) (b.logarithmPartialWithWork K).1).2 + 5 ≤ _
  change _ ≤ 12000 * (r.width + 4) ^ 2 + 2100 * (4 * r.width + 12) ^ 2 +
    K * logarithmPartialBitStep W K + 2000 * (W + 5) ^ 2 + 10
  nlinarith only [hsub, hadd, hdiv, hpartial', hmul]

def generalPowerWordBudget (a : BinaryFraction) (n : ℕ) : ℕ :=
  a.width + 3 + n * (2 * a.width + 1)

theorem powWithWork_cost_general (a : BinaryFraction) (n : ℕ) :
    (a.powWithWork n).2 ≤ 1 + n * (2000 * (generalPowerWordBudget a n + 1) ^ 2 + 1) := by
  apply powWithWork_cost_of_width
  · unfold generalPowerWordBudget
    omega
  · intro j hj
    have hw := powWithWork_width_le_storageBits a j
    rw [powWithWork_representation] at hw
    have hs := UnreducedRational.pow_storageBits a.representation j
    have hi := representation_storageBits_le a
    have hm := Nat.mul_le_mul hj.le hi
    unfold generalPowerWordBudget
    omega

theorem logarithmUniversalWordBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmUniversalWordBudget A K ≤ logarithmUniversalWordBudget B K := by
  have hquad := Nat.mul_le_mul_left (K * K) h
  have hlin := Nat.mul_le_mul_left (2 * K + 1) h
  unfold logarithmUniversalWordBudget
  omega

theorem logarithmBitBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmBitBudget A K ≤ logarithmBitBudget B K := by
  have hw := logarithmUniversalWordBudget_mono (show 8 * A + 22 ≤ 8 * B + 22 by omega) K
  have hs := Nat.mul_le_mul_left K (logarithmPartialBitStep_mono hw K)
  have h1 := Nat.mul_self_le_mul_self (show A + 4 ≤ B + 4 by omega)
  have h2 := Nat.mul_self_le_mul_self (show 4 * A + 12 ≤ 4 * B + 12 by omega)
  have h3 := Nat.mul_self_le_mul_self (show logarithmUniversalWordBudget (8 * A + 22) K + 5 ≤
      logarithmUniversalWordBudget (8 * B + 22) K + 5 by omega)
  simp only [← pow_two] at h1 h2 h3
  unfold logarithmBitBudget
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
