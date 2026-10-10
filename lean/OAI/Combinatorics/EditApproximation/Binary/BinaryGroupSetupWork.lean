import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSetup

namespace OAI

/-! Explicit bit costs of the dyadic-scale and exact sample-count builders.
The generated count determines the finite draw type. -/

namespace EditApproximation
namespace BinaryFraction

theorem signedPowerTwoWithWork_cost (e : ℤ) :
    (signedPowerTwoWithWork e).2 ≤ e.natAbs + 3 := by
  have h := Int.toNat_add_toNat_neg_eq_natAbs e
  unfold signedPowerTwoWithWork
  split_ifs <;> dsimp only <;> omega

def groupScalesBitBudget (eM eb eF : ℕ) : ℕ :=
  (7 + eM + eF) * (eM + eb + eF + 13) +
    Nat.size eM + Nat.size eb + Nat.size eF + 8

theorem groupScalesWithWork_bounds (eM eb eF : ℕ) :
    (∀ value ∈ (groupScalesWithWork eM eb eF).1,
      value.width ≤ eM + eb + eF + 7) ∧
    (groupScalesWithWork eM eb eF).2 ≤ groupScalesBitBudget eM eb eF := by
  let exponents := integerClosedRange ((eb : ℤ) - eM) ((6 + eF + eb : ℕ) : ℤ)
  have habs (e : ℤ) (he : e ∈ exponents) : e.natAbs ≤ eM + eb + eF + 6 := by
    have h := (integerClosedRange_mem _ _ _).mp he
    have hp : e ≤ (eM + eb + eF + 6 : ℕ) := by omega
    have ha : |e| ≤ (eM + eb + eF + 6 : ℕ) := abs_le.mpr ⟨by omega, hp⟩
    have hn : (e.natAbs : ℤ) ≤ (eM + eb + eF + 6 : ℕ) := by
      simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast hn
  have hlen : exponents.length = 7 + eM + eF := by
    simp only [exponents, integerClosedRange, List.length_map, List.length_range]
    omega
  constructor
  · intro value hvalue
    simp only [groupScalesWithWork, arithmeticMapWithWork_value] at hvalue
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvalue
    exact (signedPowerTwoWithWork_width e).trans (Nat.add_le_add_right (habs e he) 1)
  · have hmap := arithmeticMapWithWork_cost signedPowerTwoWithWork exponents
      (eM + eb + eF + 9) (fun e he => (signedPowerTwoWithWork_cost e).trans (by
        have h := habs e he
        omega))
    rw [hlen] at hmap
    change (arithmeticMapWithWork signedPowerTwoWithWork exponents).2 + exponents.length +
      Nat.size eM + Nat.size eb + Nat.size eF + 8 ≤ _
    unfold groupScalesBitBudget
    rw [hlen]
    nlinarith only [hmap]

def groupSampleCountWordBudget (B : ℕ) : ℕ := 64 * B + 46

def groupSampleCountBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2100 * (16 * B + 12) ^ 2 + 500 * (64 * B + 45) ^ 2 +
    4 * (65 * B + 46) + 3 * B + 8

theorem groupSampleCountWithWork_bounds (M Q b : ℕ) (h : BinaryFraction) (B : ℕ)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hh : h.width ≤ B) :
    (groupSampleCountWithWork M Q b h).1.length ≤ groupSampleCountWordBudget B ∧
      (groupSampleCountWithWork M Q b h).2 ≤ groupSampleCountBitBudget B := by
  have hMw := (nat_width_le M).trans hM
  have hQw := (nat_width_le Q).trans hQ
  have hbw := (nat_width_le b).trans hb
  have hqm := canonicalMulWithWork_width (nat Q) (nat M) B hQw hMw
  have hqmc := canonicalMulWithWork_cost (nat Q) (nat M) B hQw hMw
  have hn := canonicalMulWithWork_width (canonicalMulWithWork (nat Q) (nat M)).1 h
    (4 * B + 2) hqm (by omega)
  have hnc := canonicalMulWithWork_cost (canonicalMulWithWork (nat Q) (nat M)).1 h
    (4 * B + 2) hqm (by omega)
  have hn' : (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1.width ≤
      16 * B + 10 := by omega
  have hr := divWithWork_width_uniform
    (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
    (16 * B + 10) hn' (by omega)
  have hrc := divWithWork_cost
    (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
    (16 * B + 10) hn' (by omega)
  let ratio := divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
  change ratio.1.width ≤ _ at hr
  change ratio.2 ≤ _ at hrc
  have hceil := naturalCeilingWithWork_length ratio.1
  have hceilc := naturalCeilingWithWork_cost ratio.1
  have hsquare := Nat.pow_le_pow_left (show ratio.1.width + 1 ≤ 64 * B + 45 by omega) 2
  have hmin := wordMinWithWork_length M.bits (naturalCeilingWithWork ratio.1).1
  have hminc := wordLEWithWork_cost M.bits (naturalCeilingWithWork ratio.1).1
  simp only [Nat.size_eq_bits_len] at hmin hminc
  constructor
  · change (wordMinWithWork M.bits (naturalCeilingWithWork ratio.1).1).1.length ≤ _
    unfold groupSampleCountWordBudget
    omega
  · change _ + _ + ratio.2 + (naturalCeilingWithWork ratio.1).2 +
      (wordMinWithWork M.bits (naturalCeilingWithWork ratio.1).1).2 +
        Nat.size M + Nat.size Q + Nat.size b + 5 ≤ _
    have hword : (wordMinWithWork M.bits (naturalCeilingWithWork ratio.1).1).2 =
        (wordLEWithWork M.bits (naturalCeilingWithWork ratio.1).1).2 + 1 := rfl
    rw [hword]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hnc hrc
    unfold groupSampleCountBitBudget
    nlinarith only [hqmc, hnc, hrc, hceilc, hsquare, hminc, hceil, hM, hQ, hb, hr]

end BinaryFraction
end EditApproximation

end OAI
