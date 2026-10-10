import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddProgram

namespace OAI

section

namespace KS.W13.RationalAdd
open scoped BigOperators
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product negativeBit constructorBits pairBits)

theorem preNormalizeTicks_le (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    preNormalizeTicks sa na da sb nb db ≤ 128 * (payloadBound na da nb db) ^ 2 := by
  let S := na.length + da.length + nb.length + db.length
  have ha := KS.W06.RationalCompare.magnitude_length_le sa na
  have hb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hl := KS.W06.RationalCompare.product_length_le (magnitude sa na) db
  have hr := KS.W06.RationalCompare.product_length_le (magnitude sb nb) da
  have hd := KS.W06.RationalCompare.product_length_le da db
  have hpl := KS.W06.RationalCompare.productTicks_le (magnitude sa na) db
  have hpr := KS.W06.RationalCompare.productTicks_le (magnitude sb nb) da
  have hpd := KS.W06.RationalCompare.productTicks_le da db
  have hbl : (magnitude sa na).length + db.length + 2 ≤ S + 3 := by dsimp [S]; omega
  have hbr : (magnitude sb nb).length + da.length + 2 ≤ S + 3 := by dsimp [S]; omega
  have hbd : da.length + db.length + 2 ≤ S + 3 := by dsimp [S]; omega
  have hpl' := hpl.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hbl 2))
  have hpr' := hpr.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hbr 2))
  have hpd' := hpd.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hbd 2))
  unfold preNormalizeTicks productsTicks clearProductsTicks signedBudget payloadBound
  simp only [KS.W03.MultiplicationLoop.advance_length]
  unfold KS.W06.RationalCompare.parseTicks
  dsimp [S] at hpl' hpr' hpd'
  nlinarith [Nat.zero_le ((na.length + da.length + nb.length + db.length) ^ 2)]

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  let na := constructorBits q.num
  let da := Computability.encodeNat q.den
  let nb := constructorBits r.num
  let db := Computability.encodeNat r.den
  let S := na.length + da.length + nb.length + db.length
  let L := (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length
  have hwire : L = 2 * S + 6 := by
    have h := KS.W06.RationalCompare.pairBits_length (negativeBit q.num) na da (negativeBit r.num) nb db
    rw [KS.W06.RationalCompare.pairBits_encodeRat] at h
    exact h
  have hp := preNormalizeTicks_le (negativeBit q.num) na da (negativeBit r.num) nb db
  have hsmall : payloadBound na da nb db ≤ L + 1 := by dsimp [payloadBound]; omega
  have hlarge : payloadBound na da nb db + 1 ≤ L + 1 := by dsimp [payloadBound]; omega
  have hpow2 : (L+1)^2 ≤ (L+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp' : preNormalizeTicks (negativeBit q.num) na da (negativeBit r.num) nb db ≤ 128 * (L+1)^3 :=
    hp.trans ((Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hsmall 2)).trans (Nat.mul_le_mul_left 128 hpow2))
  have hn : 300 * (payloadBound na da nb db + 1)^3 ≤ 300 * (L+1)^3 :=
    Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left hlarge 3)
  have hout := KS.W01.rational_parts_size_le_length (q+r)
  have hsize := KS.W01.ratLength_add_le q r
  have henc (n : ℕ) : (Computability.encodeNat n).length = Nat.size n := KS.W19.encodeNat_length_eq_size n
  have hser : 16 * ((Computability.encodeNat (q+r).num.natAbs).length +
      (Computability.encodeNat (q+r).den).length + 1) ≤ 304 * (L+1)^3 := by
    rw [henc, henc]
    have hlin : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
    have hlen : KS.W01.ratLength q + KS.W01.ratLength r = L := by
      simp [L, KS.W01.ratLength]
    omega
  change _ ≤ 1000 * (L+1)^3
  unfold totalTicks
  change preNormalizeTicks (negativeBit q.num) na da (negativeBit r.num) nb db +
    300 * (payloadBound na da nb db + 1)^3 + _ ≤ _
  omega

theorem polynomial_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q+r)))
      (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) :=
  (full_spec q r).mono (totalTicks_le_polynomial q r)

theorem init_eq (input : List Bool) :
    machine.init input = ⟨some program.initial, inputState input⟩ := by
  apply congrArg (Config.mk (some program.initial))
  funext j
  fin_cases j <;> rfl

theorem output_encoded_rationals (q r : ℚ) (bits : List Bool)
    (hlen : KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ≤ bits.length) :
    machine.output (KS.W01.encodeRat q ++ KS.W01.encodeRat r) bits = KS.W01.encodeRat (q+r) := by
  have h := (polynomial_spec q r).run_of_le bits hlen
  change machine.run ⟨some program.initial, inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r)⟩ bits = _ at h
  unfold Machine.output
  rw [init_eq, h]
  rfl

theorem halts_encoded_rationals (q r : ℚ) :
    machine.HaltsWithin (KS.W01.encodeRat q ++ KS.W01.encodeRat r)
      (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
  intro seed
  have h := polynomial_spec q r (List.ofFn seed) (by simp)
  change (machine.run (machine.init (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) (List.ofFn seed)).state = none
  rw [init_eq]
  exact congrArg Config.state h

theorem intermediate_stack_length_le (q r : ℚ) (bits : List Bool)
    (hlen : bits.length ≤ KS.W29.polynomialFuel 1000 3
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) (j : Fin 16) :
    ((machine.run (machine.init (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) bits).«stacks» j).length ≤
      KS.W29.polynomialFuel 1001 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  let wire := KS.W01.encodeRat q ++ KS.W01.encodeRat r
  have hs := machine.run_stack_length_le (machine.init wire) bits j
  have hi : ((machine.init wire).«stacks» j).length ≤ wire.length := by
    simp only [Machine.init]
    split_ifs <;> simp
  have hp : wire.length + 1 ≤ (wire.length + 1)^3 := Nat.le_self_pow (by decide) _
  change bits.length ≤ 1000 * (wire.length + 1)^3 at hlen
  change ((machine.run (machine.init wire) bits).«stacks» j).length ≤ 1001 * (wire.length + 1)^3
  omega

theorem intermediate_storage_le (q r : ℚ) (bits : List Bool)
    (hlen : bits.length ≤ KS.W29.polynomialFuel 1000 3
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) :
    (∑ j : Fin 16, ((machine.run (machine.init (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) bits).«stacks» j).length) ≤
      16 * KS.W29.polynomialFuel 1001 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  calc
    _ ≤ ∑ _j : Fin 16, KS.W29.polynomialFuel 1001 3
        (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length :=
      Finset.sum_le_sum (fun j _ => intermediate_stack_length_le q r bits hlen j)
    _ = _ := by simp

theorem uniform_rational_addition :
    ∃ M : Machine, M.stackCount = 16 ∧ ∀ q r : ℚ,
      M.HaltsWithin (KS.W01.encodeRat q ++ KS.W01.encodeRat r)
        (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) ∧
      ∀ bits : List Bool,
        KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ≤ bits.length →
        M.output (KS.W01.encodeRat q ++ KS.W01.encodeRat r) bits = KS.W01.encodeRat (q+r) := by
  exact ⟨machine, rfl, fun q r => ⟨halts_encoded_rationals q r, output_encoded_rationals q r⟩⟩

end KS.W13.RationalAdd

end

end OAI
