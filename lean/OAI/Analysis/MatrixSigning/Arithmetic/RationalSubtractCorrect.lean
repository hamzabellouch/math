import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSubtractProgram

namespace OAI

section

namespace KS.W13.RationalSubtract
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem serializeTicks_le (q : ℚ) : serializeTicks q ≤ 32 * KS.W01.ratLength q + 16 := by
  obtain ⟨hn,hd⟩ := KS.W01.rational_parts_size_le_length q
  unfold serializeTicks
  simp only [KS.W19.encodeNat_length_eq_size]
  omega

theorem preparation_linear (q r : ℚ) : prepareTicks q r + changeSignTicks q r ≤
    200 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 1) := by
  have hs := serializeTicks_le q
  have hn := KS.W01.ratLength_neg_le r
  simp only [List.length_append]
  change _ ≤ 200 * (KS.W01.ratLength q + KS.W01.ratLength r + 1)
  unfold prepareTicks changeSignTicks
  omega

theorem totalTicks_le_polynomial (q r : ℚ) : totalTicks q r ≤
    KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  let L := (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length
  let N := (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)).length
  have hn := KS.W01.ratLength_neg_le r
  have hn' : N + 1 ≤ 8 * (L+1) := by
    dsimp [N,L]
    simp only [List.length_append]
    change KS.W01.ratLength q + KS.W01.ratLength (-r) + 1 ≤
      8 * (KS.W01.ratLength q + KS.W01.ratLength r + 1)
    omega
  have ha : 1000*(N+1)^3 ≤ 512000*(L+1)^3 := by
    calc
      _ ≤ 1000*(8*(L+1))^3 := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hn' 3)
      _ = _ := by ring
  have hp := preparation_linear q r
  have hlin : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
  change prepareTicks q r + changeSignTicks q r ≤ 200*(L+1) at hp
  unfold totalTicks
  change prepareTicks q r + changeSignTicks q r + 1000*(N+1)^3 ≤ 600000*(L+1)^3
  omega

theorem polynomial_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q-r)))
      (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) :=
  (full_spec q r).mono (totalTicks_le_polynomial q r)

theorem init_eq (input : List Bool) : machine.init input = ⟨some program.initial,inputState input⟩ := by
  apply congrArg (Config.mk (some program.initial))
  funext j
  fin_cases j <;> rfl

theorem output_encoded_rationals (q r : ℚ) (bits : List Bool)
    (hlen : KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ≤ bits.length) :
    machine.output (KS.W01.encodeRat q ++ KS.W01.encodeRat r) bits = KS.W01.encodeRat (q-r) := by
  have h := (polynomial_spec q r).run_of_le bits hlen
  change machine.run ⟨some program.initial, inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r)⟩ bits = _ at h
  unfold Machine.output
  rw [init_eq,h]
  rfl

theorem halts_encoded_rationals (q r : ℚ) :
    machine.HaltsWithin (KS.W01.encodeRat q ++ KS.W01.encodeRat r)
      (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
  intro seed
  have h := polynomial_spec q r (List.ofFn seed) (by simp)
  change (machine.run (machine.init (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) (List.ofFn seed)).state = none
  rw [init_eq]
  exact congrArg Config.state h

theorem output_length_le (q r : ℚ) : (KS.W01.encodeRat (q-r)).length ≤
    4 * (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 9 := by
  simpa [KS.W01.ratLength,List.length_append] using KS.W01.ratLength_sub_le q r

theorem uniform_rational_subtraction :
    ∃ M : Machine, M.stackCount = 19 ∧ ∀ q r : ℚ,
      M.HaltsWithin (KS.W01.encodeRat q ++ KS.W01.encodeRat r)
        (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) ∧
      ∀ bits : List Bool,
        KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ≤ bits.length →
        M.output (KS.W01.encodeRat q ++ KS.W01.encodeRat r) bits = KS.W01.encodeRat (q-r) := by
  exact ⟨machine,rfl,fun q r => ⟨halts_encoded_rationals q r,output_encoded_rationals q r⟩⟩

end KS.W13.RationalSubtract

end

end OAI
