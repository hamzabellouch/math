import OAI.Combinatorics.EditApproximation.Geometry.BandNumericalBits
import OAI.Combinatorics.EditApproximation.Geometry.BandEnvelopes

namespace OAI

/-! Encoding lengths of the actual finite maxima and dyadic envelopes.
These estimates include the scales below one and require no good seed. -/

namespace EditApproximation

theorem positive_rational_binary_bounds (r : ℚ) (B : ℕ)
    (hr : 0 < r) (hbits : rationalEncodingBits r ≤ B) :
    (2 : ℚ) ^ (-(B : ℤ)) ≤ r ∧ r ≤ (2 : ℚ) ^ (B : ℤ) := by
  have hnumSize : Nat.size r.num.natAbs ≤ B := by unfold rationalEncodingBits at hbits; omega
  have hdenSize : Nat.size r.den ≤ B := by unfold rationalEncodingBits at hbits; omega
  have hnum : r.num.natAbs ≤ 2 ^ B :=
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hnumSize)
  have hden : r.den ≤ 2 ^ B :=
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hdenSize)
  have hnumPos : 0 < r.num := Rat.num_pos.mpr hr
  have hnumOne : 1 ≤ r.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnumPos)
  have hrep : r = (r.num.natAbs : ℚ) / r.den := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_pos hnumPos]
    exact r.num_div_den.symm
  have hd : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hp : (0 : ℚ) < (2 : ℚ) ^ B := pow_pos (by norm_num) _
  simp only [zpow_neg, zpow_natCast]
  rw [hrep]
  constructor
  · rw [inv_eq_one_div, div_le_div_iff₀ hp hd, one_mul]
    exact_mod_cast (hden.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < r.num.natAbs)))
  · apply (div_le_iff₀ hd).mpr
    exact_mod_cast (hnum.trans (Nat.le_mul_of_pos_right _ r.den_pos))

theorem rationalDyadicCeiling_encoding (r : ℚ) (B : ℕ)
    (hr : 0 < r) (hbits : rationalEncodingBits r ≤ B) :
    rationalEncodingBits (rationalDyadicCeiling r) ≤ 5 * B + 5 := by
  have hrange := positive_rational_binary_bounds r B hr hbits
  have hlo := Int.clog_mono_right (b := 2) (zpow_pos (by norm_num : (0 : ℚ) < 2) (-(B : ℤ))) hrange.1
  have hhi := Int.clog_mono_right (b := 2) hr hrange.2
  have hclog (z : ℤ) : Int.clog 2 ((2 : ℚ) ^ z) = z := by
    simpa only [Nat.cast_ofNat] using (Int.clog_zpow (R := ℚ) (b := 2) (by decide) z)
  rw [hclog] at hlo hhi
  have htwo : rationalEncodingBits (2 : ℚ) = 4 := by
    rw [show (2 : ℚ) = (2 : ℕ) by norm_num, rationalEncodingBits_natCast]
    rfl
  unfold rationalDyadicCeiling
  cases he : Int.clog 2 r with
  | ofNat n =>
    rw [he, Int.ofNat_eq_natCast] at hlo hhi
    have hn : n ≤ B := by omega
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    have h := rationalEncodingBits_pow (2 : ℚ) n
    rw [htwo] at h
    omega
  | negSucc n =>
    rw [he, Int.negSucc_eq] at hlo hhi
    have hn : n + 1 ≤ B := by omega
    rw [zpow_negSucc]
    have hp := rationalEncodingBits_pow (2 : ℚ) (n + 1)
    have hi := rationalEncodingBits_inv ((2 : ℚ) ^ (n + 1))
    rw [htwo] at hp
    omega

theorem rationalMaximum_encoding (fallback : ℚ) (values : List ℚ) (B : ℕ)
    (hfallback : rationalEncodingBits fallback ≤ B)
    (hvalues : ∀ value ∈ values, rationalEncodingBits value ≤ B) :
    rationalEncodingBits (rationalMaximum fallback values) ≤ B := by
  induction values with
  | nil => exact hfallback
  | cons value rest ih =>
    have hv := hvalues value List.mem_cons_self
    have ht := ih (fun q hq => hvalues q (List.mem_cons_of_mem _ hq))
    change rationalEncodingBits (max value (rationalMaximum fallback rest)) ≤ B
    rcases le_total value (rationalMaximum fallback rest) with h | h
    · simpa only [max_eq_right h] using ht
    · simpa only [max_eq_left h] using hv

def bandEnvelopeEncodingBudget (M b initialBits : ℕ) : ℕ :=
  5 * max (Nat.size b + Nat.size M + 7) (initialBits + 2) + 5

theorem bandChildEnvelope_encoding {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (B : ℕ) (hb : 0 < b) (hM : 0 < M)
    (hinitial : ∀ action ∈ band, ∀ i, rationalEncodingBits (initial i (action i)) ≤ B)
    (i : Fin M) :
    rationalEncodingBits (bandChildEnvelope b band initial i) ≤ bandEnvelopeEncodingBudget M b B := by
  have hmax := rationalMaximum_encoding 0 (band.map fun action => initial i (action i)) (B + 2)
    (by norm_num [rationalEncodingBits]) (by
      intro q hq
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hq
      exact (hinitial action ha i).trans (by omega))
  have hfloor := rationalEncodingBits_div (b : ℚ) (M : ℚ)
  rw [rationalEncodingBits_natCast, rationalEncodingBits_natCast] at hfloor
  have hbits : rationalEncodingBits (max ((b : ℚ) / M)
      (rationalMaximum 0 (band.map fun action => initial i (action i)))) ≤
        max (Nat.size b + Nat.size M + 7) (B + 2) := by
    rcases le_total ((b : ℚ) / M) (rationalMaximum 0 (band.map fun action => initial i (action i))) with h | h
    · rw [max_eq_right h]
      exact hmax.trans (Nat.le_max_right _ _)
    · rw [max_eq_left h]
      exact hfloor.trans (by have h := Nat.le_max_left (Nat.size b + Nat.size M + 7) (B + 2); omega)
  exact rationalDyadicCeiling_encoding _ _
    ((div_pos (by exact_mod_cast hb) (by exact_mod_cast hM)).trans_le (le_max_left _ _)) hbits

end EditApproximation

end OAI
