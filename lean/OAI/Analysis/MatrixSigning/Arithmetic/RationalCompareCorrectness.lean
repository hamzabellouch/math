import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareProgram

namespace OAI

section

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W01

def signedFraction (negative : Bool) (num den : ℕ) : ℚ :=
  (if negative then -(num : ℚ) else num) / den

theorem fraction_le_iff (a b d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (a : ℚ) / d ≤ (b : ℚ) / e ↔ a * e ≤ b * d := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have he' : (0 : ℚ) < e := by exact_mod_cast he
  rw [div_le_div_iff₀ hd' he']
  norm_cast

theorem signedCrossLE_correct (sa sb : Bool) (a b d e : ℕ)
    (ha : sa = true → 0 < a) (hb : sb = true → 0 < b)
    (hd : 0 < d) (he : 0 < e) :
    signedCrossLE sa sb (a * e) (b * d) =
      decide (signedFraction sa a d ≤ signedFraction sb b e) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have he' : (0 : ℚ) < e := by exact_mod_cast he
  have ha0 : (0 : ℚ) ≤ (a : ℚ) / d := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hb0 : (0 : ℚ) ≤ (b : ℚ) / e := div_nonneg (Nat.cast_nonneg _) he'.le
  cases sa <;> cases sb
  · simp [signedCrossLE, signedFraction, fraction_le_iff a b d e hd he]
  · have hbpos : (0 : ℚ) < (b : ℚ) / e := div_pos (by exact_mod_cast hb rfl) he'
    have hnot : ¬ (a : ℚ) / d ≤ -((b : ℚ) / e) := by linarith
    simp [signedCrossLE, signedFraction, neg_div, hnot]
  · have hyes : -((a : ℚ) / d) ≤ (b : ℚ) / e := by linarith
    simp [signedCrossLE, signedFraction, neg_div, hyes]
  · simp [signedCrossLE, signedFraction, neg_div, neg_le_neg_iff,
      fraction_le_iff b a e d he hd]

theorem magnitude_constructor_value (z : ℤ) :
    KS.W19.bitsValue (magnitude (negativeBit z) (constructorBits z)) = z.natAbs := by
  rw [magnitude, KS.W01.MagnitudeProgram.result_value]
  simp only [constructorBits, KS.W19.bitsValue_encodeNat]
  cases z <;> simp [negativeBit, intPayload, KS.W19.digit]

theorem negativeBit_pos (z : ℤ) (h : negativeBit z = true) : 0 < z.natAbs := by
  cases z <;> simp_all [negativeBit]
  omega

theorem signedFraction_num_den (q : ℚ) :
    signedFraction (negativeBit q.num) q.num.natAbs q.den = q := by
  have hn : (if negativeBit q.num then -(q.num.natAbs : ℚ) else (q.num.natAbs : ℚ)) =
      (q.num : ℚ) := by
    cases q.num <;> simp [negativeBit, Int.cast_negSucc]
  unfold signedFraction
  rw [hn]
  exact q.num_div_den

theorem canonical_final_output (q r : ℚ) :
    finalStacks (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
      (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den) 9 =
      [decide (q ≤ r)] := by
  rw [final_output, magnitude_constructor_value, magnitude_constructor_value,
    KS.W19.bitsValue_encodeNat, KS.W19.bitsValue_encodeNat,
    signedCrossLE_correct _ _ _ _ _ _ (negativeBit_pos q.num) (negativeBit_pos r.num)
      q.den_pos r.den_pos, signedFraction_num_den, signedFraction_num_den]

theorem magnitude_length_le (s : Bool) (xs : List Bool) :
    (magnitude s xs).length ≤ xs.length + 1 := by
  simpa [magnitude, KS.W01.MagnitudeProgram.result] using
    KS.W01.BinaryAdder.addBits_length_le s [] xs

theorem product_length_le (xs ys : List Bool) :
    (product xs ys).length ≤ xs.length + ys.length := by
  simpa [product, KS.W03.BinaryMultiply.multiply, KS.W19.trimBits_eq_encodeNat,
    KS.W03.BinaryMultiply.multiplyRaw_correct] using KS.W03.BinaryMultiply.multiply_length_le xs ys

theorem totalTicks_le_polynomial (sa : Bool) (na da : List Bool)
    (sb : Bool) (nb db : List Bool) :
    totalTicks sa na da sb nb db ≤
      KS.W29.polynomialFuel 128 2 (pairBits sa na da sb nb db).length := by
  let S := na.length + da.length + nb.length + db.length
  have hma := magnitude_length_le sa na
  have hmb := magnitude_length_le sb nb
  have hla := product_length_le (magnitude sa na) db
  have hlb := product_length_le (magnitude sb nb) da
  have hpa := productTicks_le (magnitude sa na) db
  have hpb := productTicks_le (magnitude sb nb) da
  have hwa : (magnitude sa na).length + db.length + 2 ≤ S + 3 := by unfold S; omega
  have hwb : (magnitude sb nb).length + da.length + 2 ≤ S + 3 := by unfold S; omega
  have hpa' := hpa.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hwa 2))
  have hpb' := hpb.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hwb 2))
  have hbound : totalTicks sa na da sb nb db ≤ 64 * (S + 3) ^ 2 := by
    unfold totalTicks parseTicks
    dsimp only
    unfold S at hpa' hpb' ⊢
    nlinarith [Nat.zero_le ((na.length + da.length + nb.length + db.length) ^ 2)]
  apply hbound.trans
  unfold KS.W29.polynomialFuel
  rw [pairBits_length]
  have hL : S + 3 ≤ 2 * (na.length + da.length + nb.length + db.length) + 6 + 1 := by
    unfold S
    omega
  exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hL 2)

theorem canonical_comparison_spec (q r : ℚ) :
    KS.W03.MachineCombinators.RunSpec program
      (fields (encodeRat q ++ encodeRat r) [] [] [] [] [] [])
      (finalStacks (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
        (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den))
      (KS.W29.polynomialFuel 128 2 (encodeRat q ++ encodeRat r).length) := by
  have h := full_spec (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
    (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den)
  have ht := totalTicks_le_polynomial (negativeBit q.num) (constructorBits q.num)
    (Computability.encodeNat q.den) (negativeBit r.num) (constructorBits r.num)
    (Computability.encodeNat r.den)
  rw [pairBits_encodeRat] at h ht
  exact h.mono ht

theorem output_encoded_rationals (q r : ℚ) (bits : List Bool)
    (hlen : KS.W29.polynomialFuel 128 2 (encodeRat q ++ encodeRat r).length ≤ bits.length) :
    machine.output (encodeRat q ++ encodeRat r) bits = [decide (q ≤ r)] := by
  have ht := totalTicks_le_polynomial (negativeBit q.num) (constructorBits q.num)
    (Computability.encodeNat q.den) (negativeBit r.num) (constructorBits r.num)
    (Computability.encodeNat r.den)
  rw [pairBits_encodeRat] at ht
  have hr := run_input (negativeBit q.num) (constructorBits q.num)
    (Computability.encodeNat q.den) (negativeBit r.num) (constructorBits r.num)
    (Computability.encodeNat r.den) bits (ht.trans hlen)
  rw [pairBits_encodeRat] at hr
  unfold Machine.output
  rw [hr]
  exact canonical_final_output q r

theorem halts_encoded_rationals (q r : ℚ) :
    machine.HaltsWithin (encodeRat q ++ encodeRat r)
      (KS.W29.polynomialFuel 128 2 (encodeRat q ++ encodeRat r).length) := by
  intro seed
  have ht := totalTicks_le_polynomial (negativeBit q.num) (constructorBits q.num)
    (Computability.encodeNat q.den) (negativeBit r.num) (constructorBits r.num)
    (Computability.encodeNat r.den)
  rw [pairBits_encodeRat] at ht
  have hr := run_input (negativeBit q.num) (constructorBits q.num)
    (Computability.encodeNat q.den) (negativeBit r.num) (constructorBits r.num)
    (Computability.encodeNat r.den) (List.ofFn seed) (by simpa using ht)
  rw [pairBits_encodeRat] at hr
  exact congrArg Config.state hr

theorem uniform_rational_comparison :
    ∃ M : Machine, M.stackCount = 13 ∧ ∀ q r : ℚ,
      M.HaltsWithin (encodeRat q ++ encodeRat r)
        (KS.W29.polynomialFuel 128 2 (encodeRat q ++ encodeRat r).length) ∧
      ∀ bits : List Bool,
        KS.W29.polynomialFuel 128 2 (encodeRat q ++ encodeRat r).length ≤ bits.length →
        M.output (encodeRat q ++ encodeRat r) bits = [decide (q ≤ r)] := by
  exact ⟨machine, rfl, fun q r => ⟨halts_encoded_rationals q r, output_encoded_rationals q r⟩⟩

end KS.W06.RationalCompare

end

end OAI
