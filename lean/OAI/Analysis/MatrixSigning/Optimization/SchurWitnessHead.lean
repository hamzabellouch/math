import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.NegativeDivision

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

def schurHead {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℚ :=
  -((∑ j : Fin n, DenseRatMatrix.decode M 0 j.succ * y j) / DenseRatMatrix.decode M 0 0)

def fetchPivotProgram : Program 29 := compose copyDimension readProgram

def schurHeadProgram : Program 29 := compose (compose (compose program fetchPivotProgram)
  (StackTransfer.program 17 0 26)) negativeDivisionProgram

def schurHeadTicks {n : ℕ} (M : DenseRatMatrix (n + 1)) (b : ℕ) (y : Fin n → ℚ) : ℕ :=
  totalTicks M b (zeroPadded y) 0 +
  ((2 * (Computability.encodeNat (n + 1)).length + 2) + 1024 * (n + 2) ^ 2 * (b + 1)) +
  (2 * (KS.W01.encodeRat ((DenseRatMatrix.decode M *ᵥ zeroPadded y) 0)).length + 2) +
  negativeDivisionTicks ((DenseRatMatrix.decode M *ᵥ zeroPadded y) 0) (DenseRatMatrix.decode M 0 0)

theorem schurHead_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (y : Fin n → ℚ) :
    RunSpec schurHeadProgram (initialStacks M (zeroPadded y) 0)
      (put (initialStacks M (zeroPadded y) 0) 10 (KS.W01.encodeRat (schurHead M y)))
      (schurHeadTicks M b y) := by
  let z := (DenseRatMatrix.decode M *ᵥ zeroPadded y) 0
  let pivot := DenseRatMatrix.decode M 0 0
  let saved := initialStacks M (zeroPadded y) 0
  let s := put saved 17 (KS.W01.encodeRat z)
  let t := put s 2 (Computability.encodeNat (n + 1))
  let u := put s 0 (KS.W01.encodeRat pivot)
  have h1 := full_spec M b hnum hden (zeroPadded y) 0
  have h2 : RunSpec copyDimension s t (2 * (Computability.encodeNat (n + 1)).length + 2) :=
    copy_spec 22 2 (by decide) (by decide) (by decide) s rfl rfl
  have h3 : RunSpec readProgram t u (1024 * (n + 2) ^ 2 * (b + 1)) := by
    convert read_spec M b hnum hden 0 0 s rfl (by intro j; fin_cases j <;> rfl) using 1
    funext j
    fin_cases j <;>
      simp [t, s, readBefore, put, saved, initialStacks, state, Computability.encodeNat] <;> rfl
  have h4 : RunSpec (StackTransfer.program 17 0 26) u
      (arithmeticState saved (KS.W01.encodeRat z ++ KS.W01.encodeRat pivot) [])
      (2 * (KS.W01.encodeRat z).length + 2) := by
    convert StackTransfer.spec (17 : Fin 29) 0 26 (by decide) (by decide) (by decide) u rfl using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [u, s, saved, initialStacks, state, arithmeticState, StackTransfer.after, put]
  have h5 := negativeDivision_spec saved z pivot (by rfl)
  have h := ((h1.compose (h2.compose h3)).compose h4).compose h5
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [schurHead, z, pivot, saved, put, arithmeticState, initialStacks, state,
    zeroPadded_row_dot]

theorem schurHeadTicks_stored {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    schurHeadTicks M (storedLength M (zeroPadded y) 0) y ≤
      KS.W29.polynomialFuel 10000000000000000 8 (storedLength M (zeroPadded y) 0) := by
  let L := storedLength M (zeroPadded y) 0
  let z := (DenseRatMatrix.decode M *ᵥ zeroPadded y) 0
  let p := DenseRatMatrix.decode M 0 0
  have hbase := totalTicks_stored M (zeroPadded y) 0
  have hw := pair_stream_length M (zeroPadded y) 0
  have hz := FixedDot.dotValue_length_le_wire (rowPairs M 0 (indexedVector (zeroPadded y)))
  rw [rowPairs_dotValue] at hz
  have hp := matrix_entry_length M 0 0
  have hp' : KS.W01.ratLength p ≤ L := by dsimp [p, L, storedLength]; omega
  have hn : n + 1 ≤ L := by
    have h := dimension_le_vector (zeroPadded y)
    dsimp [L, storedLength]; omega
  have hnwire : (Computability.encodeNat (n + 1)).length ≤ L := by
    dsimp [L, storedLength]; omega
  have hz' : KS.W01.ratLength z ≤ 167 * (L + 1) ^ 2 := by
    dsimp [z, L] at *
    nlinarith
  have hpw : (KS.W01.encodeRat z ++ KS.W01.encodeRat p).length + 1 ≤ 168 * (L + 1) ^ 2 := by
    simp only [List.length_append]
    change KS.W01.ratLength z + KS.W01.ratLength p + 1 ≤ _
    nlinarith
  have hneg : negativeDivisionTicks z p ≤ 474163200000000 * (L + 1) ^ 6 := by
    calc
      _ ≤ 100000000 * ((KS.W01.encodeRat z ++ KS.W01.encodeRat p).length + 1) ^ 3 :=
        negativeDivisionTicks_le z p
      _ ≤ 100000000 * (168 * (L + 1) ^ 2) ^ 3 := by gcongr
      _ = _ := by ring
  have hr : 1024 * (n + 2) ^ 2 * (L + 1) ≤ 1024 * (L + 1) ^ 3 := by
    calc
      _ ≤ 1024 * (L + 1) ^ 2 * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul_left 1024
          (Nat.pow_le_pow_left (show n + 2 ≤ L + 1 by omega) 2))
      _ = _ := by ring
  have h6 : (L + 1) ^ 6 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : (L + 1) ^ 3 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (L + 1) ^ 2 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : L + 1 ≤ (L + 1) ^ 8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (n := L + 1) (by omega) (show 1 ≤ 8 by decide))
  unfold schurHeadTicks KS.W29.polynomialFuel
  change _ ≤ 10000000000000000 * (L + 1) ^ 8
  change totalTicks M L (zeroPadded y) 0 ≤ 1000000000000 * (L + 1) ^ 8 at hbase
  dsimp only [z, p, L] at *
  unfold KS.W01.ratLength at hz'
  omega

theorem schurHead_polynomial_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    RunSpec schurHeadProgram (initialStacks M (zeroPadded y) 0)
      (put (initialStacks M (zeroPadded y) 0) 10 (KS.W01.encodeRat (schurHead M y)))
      (KS.W29.polynomialFuel 10000000000000000 8 (storedLength M (zeroPadded y) 0)) := by
  obtain ⟨hn, hd⟩ := matrix_parts_stored M (zeroPadded y) 0
  exact (schurHead_spec M _ hn hd y).mono (schurHeadTicks_stored M y)

end KS.W12.RowDot

end OAI
