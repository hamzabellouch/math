import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedDotBounds
import OAI.Analysis.MatrixSigning.Matrices.RowDotMachine

namespace OAI

section

namespace KS.W12.RowDot
open Matrix
open KS.W01 KS.W01.FixedStack KS.W07
open scoped BigOperators

def storedLength {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) : ℕ :=
  (KS.W08.denseMatrixTape M).length + (vectorTape x).length +
  (Computability.encodeNat i.val).length + (Computability.encodeNat n).length

theorem payload_le_framed (xs : List (List Bool)) (p : List Bool) (hp : p ∈ xs) :
    p.length ≤ (xs.flatMap frame).length := by
  induction xs with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      simp only [List.flatMap_cons, List.length_append, length_frame]
      rcases hp with rfl | hp
      · omega
      · have h := ih hp; omega

theorem count_le_framed (xs : List (List Bool)) : xs.length ≤ (xs.flatMap frame).length := by
  induction xs with
  | nil => simp
  | cons q qs ih => simp only [List.length_cons, List.flatMap_cons, List.length_append, length_frame]; omega

theorem matrix_entry_length {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    ratLength (DenseRatMatrix.decode M i j) ≤ (KS.W08.denseMatrixTape M).length := by
  apply payload_le_framed
  have h := List.getElem_mem (l := KS.W08.denseMatrixPayloads M)
    (n := i.val * n + j.val) (by simpa using KS.W08.matrixEntryIndex_lt i j)
  simpa only [KS.W08.denseMatrixPayloads_get] using h

theorem vector_entry_length {n : ℕ} (x : Fin n → ℚ) (j : Fin n) :
    ratLength (x j) ≤ (vectorTape x).length := by
  apply payload_le_framed
  simp only [List.mem_ofFn]
  exact ⟨j, rfl⟩

theorem dimension_le_vector {n : ℕ} (x : Fin n → ℚ) : n ≤ (vectorTape x).length := by
  simpa [vectorTape] using count_le_framed (List.ofFn (fun j => encodeRat (x j)))

theorem matrix_parts_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    (∀ j k, (DenseRatMatrix.decode M j k).num.natAbs ≤ 2 ^ storedLength M x i) ∧
    (∀ j k, (DenseRatMatrix.decode M j k).den ≤ 2 ^ storedLength M x i) := by
  have hlen : ∀ j k, ratLength (DenseRatMatrix.decode M j k) ≤ storedLength M x i := by
    intro j k
    have h := matrix_entry_length M j k
    unfold storedLength
    omega
  constructor <;> intro j k
  · exact (rational_parts_le_two_pow_length _).1.trans (Nat.pow_le_pow_right (by decide) (hlen j k))
  · exact (rational_parts_le_two_pow_length _).2.trans (Nat.pow_le_pow_right (by decide) (hlen j k))

theorem encodeNat_length_le_self (k : ℕ) : (Computability.encodeNat k).length ≤ k := by
  rw [KS.W19.encodeNat_length_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem pair_stream_length {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    (FixedDot.inputWire (rowPairs M i (indexedVector x))).length ≤
      5 * (storedLength M x i + 1) ^ 2 := by
  have hn : n ≤ storedLength M x i := by
    have h := dimension_le_vector x
    unfold storedLength
    omega
  have hsum : (FixedDot.inputWire (rowPairs M i (indexedVector x))).length ≤
      n * (4 * storedLength M x i + 1) := by
    simp only [rowPairs, indexedVector, List.map_ofFn, FixedDot.inputWire,
      List.length_flatMap, List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _j : Fin n, (4 * storedLength M x i + 1) := by
        apply Finset.sum_le_sum
        intro j _
        have ha := matrix_entry_length M i j
        have hq := vector_entry_length x j
        simp only [Function.comp_def, FixedDot.pairWire_length, FixedDot.pairPayload,
          List.length_append]
        unfold ratLength at ha hq
        unfold storedLength
        omega
      _ = _ := by simp
  calc
    _ ≤ n * (4 * storedLength M x i + 1) := hsum
    _ ≤ storedLength M x i * (4 * storedLength M x i + 1) := Nat.mul_le_mul_right _ hn
    _ ≤ _ := by nlinarith

theorem bodyTicks_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i j : Fin n) :
    bodyTicks M (storedLength M x i) i (j, x j) ≤ 2000 * (storedLength M x i + 1) ^ 3 := by
  let L := storedLength M x i
  have hn : n ≤ L := by have h := dimension_le_vector x; dsimp [L, storedLength]; omega
  have hi : i.val ≤ L := i.isLt.le.trans hn
  have hj : j.val ≤ L := j.isLt.le.trans hn
  have hni := encodeNat_length_le_self i.val
  have hnj := encodeNat_length_le_self j.val
  have hnn := encodeNat_length_le_self n
  have hnjs := encodeNat_length_le_self (j.val + 1)
  have ha := matrix_entry_length M i j
  have hq := vector_entry_length x j
  have hla : (encodeRat (DenseRatMatrix.decode M i j)).length ≤ L := by
    dsimp [L, storedLength]; unfold ratLength at ha; omega
  have hlq : (encodeRat (x j)).length ≤ L := by
    dsimp [L, storedLength]; unfold ratLength at hq; omega
  have had := KS.W13.RationalAdd.canonicalAddTicks_le (Computability.encodeNat j.val) [true]
  have hread : 1024 * (n + 1) ^ 2 * (L + 1) ≤ 1024 * (L + 1) ^ 3 := by
    calc
      _ ≤ 1024 * (L + 1) ^ 2 * (L + 1) := by gcongr
      _ = _ := by ring
  unfold bodyTicks collectTicks pairTicks incrementTicks
  simp only [List.length_append, KS.W01.length_frame, List.length_cons, List.length_nil] at *
  change _ ≤ 2000 * (L + 1) ^ 3
  have hl : 60 * L + 60 ≤ 976 * (L + 1) ^ 3 := by nlinarith [Nat.zero_le (L ^ 3)]
  dsimp only [L] at *
  omega

theorem loopTicks_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    loopTicks M (storedLength M x i) i (indexedVector x) ≤
      3000 * (storedLength M x i + 1) ^ 4 := by
  let L := storedLength M x i
  have haux : ∀ xs : List (Fin n × ℚ), (∀ p ∈ xs, p.2 = x p.1) →
      loopTicks M L i xs ≤ 1 + xs.length * (1 + 2000 * (L + 1) ^ 3) := by
    intro xs hx
    induction xs with
    | nil => simp [loopTicks]
    | cons p ps ih =>
        have hp := hx p (by simp)
        have ht := ih (by intro q hq; exact hx q (by simp [hq]))
        have hb := bodyTicks_stored M x i p.1
        rw [← hp] at hb
        simp only [loopTicks, List.length_cons]
        dsimp only [L] at *
        nlinarith
  have h := haux (indexedVector x) (by intro p hp; simp [indexedVector] at hp; rcases hp with ⟨j, rfl⟩; rfl)
  have hn : n ≤ L := by have h := dimension_le_vector x; dsimp [L, storedLength]; omega
  simp only [indexedVector, List.length_ofFn] at h
  calc
    _ ≤ 1 + n * (1 + 2000 * (L + 1) ^ 3) := h
    _ ≤ 1 + L * (1 + 2000 * (L + 1) ^ 3) := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (L ^ 2), Nat.zero_le (L ^ 3)]

theorem totalTicks_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    totalTicks M (storedLength M x i) x i ≤
      KS.W29.polynomialFuel 1000000000000 8 (storedLength M x i) := by
  let L := storedLength M x i
  let ps := rowPairs M i (indexedVector x)
  have hloop := loopTicks_stored M x i
  have hwire := pair_stream_length M x i
  have hdot := FixedDot.totalTicks_le_polynomial ps
  have hv : (vectorTape x).length ≤ L := by dsimp [L, storedLength]; omega
  have hn : (Computability.encodeNat n).length ≤ L := by dsimp [L, storedLength]; omega
  have hw1 : (FixedDot.inputWire ps).length + 1 ≤ 6 * (L + 1) ^ 2 := by
    dsimp [ps, L] at *
    nlinarith
  have hp : ((FixedDot.inputWire ps).length + 1) ^ 4 ≤ (6 * (L + 1) ^ 2) ^ 4 := by gcongr
  have hdot' : FixedDot.totalTicks ps ≤ 259200000000 * (L + 1) ^ 8 := by
    calc
      _ ≤ 200000000 * ((FixedDot.inputWire ps).length + 1) ^ 4 := hdot
      _ ≤ 200000000 * (6 * (L + 1) ^ 2) ^ 4 := Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  have hgrow : (L + 1) ^ 4 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hgrow2 : (L + 1) ^ 2 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hgrow1 : L + 1 ≤ (L + 1) ^ 8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (n := L + 1) (by omega) (show 1 ≤ 8 by decide))
  unfold totalTicks prepareTicks finishTicks KS.W29.polynomialFuel
  change _ ≤ 1000000000000 * (L + 1) ^ 8
  dsimp only [L, ps] at *
  omega

theorem polynomial_spec {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    KS.W03.MachineCombinators.RunSpec program (initialStacks M x i)
      (put (initialStacks M x i) 17 (encodeRat ((DenseRatMatrix.decode M *ᵥ x) i)))
      (KS.W29.polynomialFuel 1000000000000 8 (storedLength M x i)) := by
  obtain ⟨hn, hd⟩ := matrix_parts_stored M x i
  exact (full_spec M (storedLength M x i) hn hd x i).mono (totalTicks_stored M x i)

end KS.W12.RowDot

end

end OAI
