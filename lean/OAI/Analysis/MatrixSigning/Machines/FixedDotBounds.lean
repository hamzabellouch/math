import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddCorrect
import OAI.Analysis.MatrixSigning.Encoding.SumEncodingSize
import OAI.Analysis.MatrixSigning.Machines.FixedDotMachine

namespace OAI

namespace KS.W12.FixedDot
open KS.W01 KS.W01.FixedStack KS.W29.FixedSequential

@[simp] theorem inputWire_append (xs ys : List (ℚ × ℚ)) :
    inputWire (xs ++ ys) = inputWire xs ++ inputWire ys := by simp [inputWire]

@[simp] theorem dotValue_append (xs ys : List (ℚ × ℚ)) :
    dotValue (xs ++ ys) = dotValue xs + dotValue ys := by simp [dotValue]

theorem count_le_wire (ps : List (ℚ × ℚ)) : ps.length ≤ (inputWire ps).length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [inputWire_cons, List.length_append, pairWire_length, List.length_cons]
      omega

theorem pairPayload_le_wire (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) (hp : p ∈ ps) :
    (pairPayload p).length ≤ (inputWire ps).length := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
      simp only [List.mem_cons] at hp
      simp only [inputWire_cons, List.length_append, pairWire_length]
      rcases hp with rfl | hp
      · omega
      · have h := ih hp
        omega

theorem product_sumBudget_le_wire (ps : List (ℚ × ℚ)) :
    ((ps.map (fun p => p.1 * p.2)).map ratLength).sum + ps.length ≤
      8 * (inputWire ps).length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hm := ratLength_mul_le p.1 p.2
      have hp : ratLength p.1 + ratLength p.2 = (pairPayload p).length := by
        simp [ratLength, pairPayload]
      rw [hp] at hm
      simp only [List.map_cons, List.sum_cons, List.length_cons, inputWire_cons,
        List.length_append, pairWire_length]
      omega

theorem dotValue_length_le_wire (ps : List (ℚ × ℚ)) :
    ratLength (dotValue ps) ≤ 32 * (inputWire ps).length + 7 := by
  have hs := ratLength_sum_le (ps.map (fun p => p.1 * p.2))
  have hb := product_sumBudget_le_wire ps
  simp only [List.length_map] at hs
  exact hs.trans (by omega)

theorem bodyTicks_le_uniform (p : ℚ × ℚ) (a : ℚ) (L : ℕ)
    (hp : (pairPayload p).length ≤ L) (ha : ratLength a ≤ 32 * L + 7) :
    bodyTicks p a ≤ 100000000 * (L + 1) ^ 3 := by
  have hprod := ratLength_mul_le p.1 p.2
  have hpl : ratLength p.1 + ratLength p.2 = (pairPayload p).length := by
    simp [ratLength, pairPayload]
  rw [hpl] at hprod
  have hprod' : ratLength (p.1 * p.2) ≤ 4 * L + 7 := by omega
  have hsum := ratLength_add_le a (p.1 * p.2)
  have hsum' : ratLength (a + p.1 * p.2) ≤ 144 * L + 65 := by omega
  have hmul : KS.W15.RationalMultiply.totalTicks p.1 p.2 ≤ 2048 * (L + 1) ^ 3 := by
    apply (KS.W15.RationalMultiply.totalTicks_le_polynomial p.1 p.2).trans
    apply Nat.mul_le_mul_left 2048
    apply Nat.pow_le_pow_left
    simpa [KS.W15.RationalMultiply.inputBits, pairPayload] using Nat.add_le_add_right hp 1
  have hinput : (encodeRat a ++ encodeRat (p.1 * p.2)).length + 1 ≤ 36 * (L + 1) := by
    simp only [List.length_append]
    change ratLength a + ratLength (p.1 * p.2) + 1 ≤ 36 * (L + 1)
    omega
  have hadd0 := (KS.W13.RationalAdd.totalTicks_le_polynomial a (p.1 * p.2)).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hinput 3))
  have hadd : KS.W13.RationalAdd.totalTicks a (p.1 * p.2) ≤ 46656000 * (L + 1) ^ 3 := by
    convert hadd0 using 1
    ring
  have hcube : L + 1 ≤ (L + 1) ^ 3 := by
    calc
      L + 1 = (L + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [ratLength] at ha hprod' hsum'
  unfold bodyTicks
  omega

theorem loopTicks_le_prefix_budget (all : List (ℚ × ℚ)) (C : ℕ)
    (hbody : ∀ pre p post, pre ++ p :: post = all → bodyTicks p (dotValue pre) ≤ C)
    (pre rest : List (ℚ × ℚ)) (hsplit : pre ++ rest = all) :
    loopTicks bodyTicks rest (dotValue pre) ≤ rest.length * (C + 1) + 1 := by
  induction rest generalizing pre with
  | nil => simp [loopTicks]
  | cons p rest ih =>
      have hb := hbody pre p rest hsplit
      have hs : (pre ++ [p]) ++ rest = all := by simpa only [List.append_assoc, List.singleton_append] using hsplit
      have ht := ih (pre ++ [p]) hs
      have hv : dotValue (pre ++ [p]) = dotValue pre + p.1 * p.2 := by
        simp [dotValue_append]
      rw [hv] at ht
      simp only [loopTicks, List.length_cons]
      nlinarith

theorem totalTicks_le_polynomial (ps : List (ℚ × ℚ)) :
    totalTicks ps ≤ KS.W29.polynomialFuel 200000000 4 (inputWire ps).length := by
  let L := (inputWire ps).length
  let C := 100000000 * (L + 1) ^ 3
  have hb : ∀ pre p post, pre ++ p :: post = ps → bodyTicks p (dotValue pre) ≤ C := by
    intro pre p post hsplit
    apply bodyTicks_le_uniform p (dotValue pre) L
    · apply pairPayload_le_wire p ps
      rw [← hsplit]
      simp
    · have hpre : (inputWire pre).length ≤ L := by
        dsimp [L]
        rw [← hsplit, inputWire_append, List.length_append]
        omega
      exact (dotValue_length_le_wire pre).trans (by omega)
  have hl := loopTicks_le_prefix_budget ps C hb [] ps rfl
  have hn : ps.length ≤ L := count_le_wire ps
  simp only [dotValue_nil] at hl
  have ht : totalTicks ps ≤ L * (C + 1) + 6 := by
    have hm := Nat.mul_le_mul_right (C + 1) hn
    unfold totalTicks
    omega
  have hN : 1 ≤ L + 1 := by omega
  have hp : 1 ≤ (L + 1) ^ 4 := by
    simpa only [one_pow] using Nat.pow_le_pow_left hN 4
  have hL : L ≤ (L + 1) ^ 4 := by
    calc
      L ≤ L + 1 := by omega
      _ = (L + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hc : L * C ≤ 100000000 * (L + 1) ^ 4 := by
    have hm := Nat.mul_le_mul_right ((L + 1) ^ 3) (show L ≤ L + 1 by omega)
    calc
      L * C = 100000000 * (L * (L + 1) ^ 3) := by dsimp [C]; ring
      _ ≤ 100000000 * ((L + 1) * (L + 1) ^ 3) := Nat.mul_le_mul_left _ hm
      _ = 100000000 * (L + 1) ^ 4 := by ring
  change totalTicks ps ≤ 200000000 * (L + 1) ^ 4
  simp only [Nat.mul_add, Nat.mul_one] at ht
  omega

theorem halts_input_polynomial (ps : List (ℚ × ℚ)) :
    machine.HaltsWithin (inputWire ps)
      (KS.W29.polynomialFuel 200000000 4 (inputWire ps).length) := by
  intro seed
  change (machine.run (machine.init (inputWire ps)) (List.ofFn seed)).state = none
  rw [run_input ps (List.ofFn seed) (by
    simpa only [List.length_ofFn] using totalTicks_le_polynomial ps)]

theorem transient_payload_polynomial (ps : List (ℚ × ℚ)) (bits : List Bool)
    (hlen : bits.length ≤ KS.W29.polynomialFuel 200000000 4 (inputWire ps).length)
    (j : Fin 19) :
    ((machine.run (machine.init (inputWire ps)) bits).«stacks» j).length ≤
      (inputWire ps).length + KS.W29.polynomialFuel 200000000 4 (inputWire ps).length :=
  (transient_payload ps bits j).trans (Nat.add_le_add_left hlen _)

theorem uniform_rational_dot_product :
    ∃ M : Machine, M.stackCount = 19 ∧ M.inputStack.val = 16 ∧ M.outputStack.val = 17 ∧
      ∀ ps : List (ℚ × ℚ),
        M.HaltsWithin (inputWire ps) (KS.W29.polynomialFuel 200000000 4 (inputWire ps).length) ∧
        ∀ bits : List Bool,
          KS.W29.polynomialFuel 200000000 4 (inputWire ps).length ≤ bits.length →
          M.output (inputWire ps) bits = encodeRat (dotValue ps) := by
  refine ⟨machine, rfl, rfl, rfl, ?_⟩
  intro ps
  refine ⟨halts_input_polynomial ps, ?_⟩
  intro bits hbits
  exact output_correct ps bits ((totalTicks_le_polynomial ps).trans hbits)

end KS.W12.FixedDot

end OAI
