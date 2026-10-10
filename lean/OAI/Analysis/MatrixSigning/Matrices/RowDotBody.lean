import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RowDotCounter
import OAI.Analysis.MatrixSigning.Matrices.RowDotModel
import OAI.Analysis.MatrixSigning.Matrices.RowDotPrimitives

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def copyColumn : Program 29 := copyProgram 24 0 (by decide) (by decide) (by decide)
def copyRow : Program 29 := copyProgram 21 1 (by decide) (by decide) (by decide)
def copyDimension : Program 29 := copyProgram 22 2 (by decide) (by decide) (by decide)
def collectProgram : Program 29 :=
  compose (compose (compose (compose decodeProgram copyColumn) copyRow) copyDimension) readProgram

def pairProgram : Program 29 := compose (compose (compose
  (StackTransfer.program 27 28 26) (StackTransfer.program 0 28 26)) frameProgram) appendProgram

def body : Program 29 := compose (compose collectProgram pairProgram) incrementProgram

def collectTicks (n b k row : ℕ) (q : ℚ) : ℕ :=
  3 * (KS.W01.encodeRat q).length + 2 +
  (2 * (Computability.encodeNat k).length + 2) +
  (2 * (Computability.encodeNat row).length + 2) +
  (2 * (Computability.encodeNat n).length + 2) + 1024 * (n + 1) ^ 2 * (b + 1)

def pairTicks (a q : ℚ) : ℕ :=
  (2 * (KS.W01.encodeRat q).length + 2) + (2 * (KS.W01.encodeRat a).length + 2) +
  (4 * (KS.W01.encodeRat a ++ KS.W01.encodeRat q).length + 3) +
  ((KS.W01.frame (KS.W01.encodeRat a ++ KS.W01.encodeRat q)).length + 1)

def bodyTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (i : Fin n)
    (p : Fin n × ℚ) : ℕ := collectTicks n b p.1.val i.val p.2 +
  pairTicks (KS.W07.DenseRatMatrix.decode M i p.1) p.2 + incrementTicks p.1.val

theorem collect_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) (out : List Bool) :
    RunSpec collectProgram (boundary M x i (p :: xs) p.1.val out)
      (put (put (boundary M x i xs p.1.val out) 27 (KS.W01.encodeRat p.2))
        0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i p.1)))
      (collectTicks n b p.1.val i.val p.2) := by
  let s0 := boundary M x i (p :: xs) p.1.val out
  let s1 := put (boundary M x i xs p.1.val out) 27 (KS.W01.encodeRat p.2)
  let s2 := put s1 0 (Computability.encodeNat p.1.val)
  let s3 := put s2 1 (Computability.encodeNat i.val)
  let s4 := put s3 2 (Computability.encodeNat n)
  have h1 : RunSpec decodeProgram s0 s1 (3 * (KS.W01.encodeRat p.2).length + 2) := by
    convert decode_spec s0 (KS.W01.encodeRat p.2) (tailTape xs) rfl rfl rfl using 1
    funext j
    fin_cases j <;> simp [s0, s1, boundary, state, put]
  have h2 : RunSpec copyColumn s1 s2 (2 * (Computability.encodeNat p.1.val).length + 2) :=
    copy_spec 24 0 (by decide) (by decide) (by decide) s1 rfl rfl
  have h3 : RunSpec copyRow s2 s3 (2 * (Computability.encodeNat i.val).length + 2) :=
    copy_spec 21 1 (by decide) (by decide) (by decide) s2 rfl rfl
  have h4 : RunSpec copyDimension s3 s4 (2 * (Computability.encodeNat n).length + 2) :=
    copy_spec 22 2 (by decide) (by decide) (by decide) s3 rfl rfl
  have h5 : RunSpec readProgram s4
      (put s1 0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i p.1)))
      (1024 * (n + 1) ^ 2 * (b + 1)) := by
    exact read_spec M b hnum hden i p.1 s1 rfl (by intro r; fin_cases r <;> rfl)
  exact (((h1.compose h2).compose h3).compose h4).compose h5

theorem pair_spec (s : Fin 29 → List Bool) (a q : ℚ)
    (h0 : s 0 = KS.W01.encodeRat a) (h27 : s 27 = KS.W01.encodeRat q)
    (h4 : s 4 = []) (h26 : s 26 = []) (h28 : s 28 = []) :
    RunSpec pairProgram s
      (put (put (put s 0 []) 27 []) 25
        ((FixedDot.pairWire (a, q)).reverse ++ s 25)) (pairTicks a q) := by
  let s1 := StackTransfer.after 27 28 s
  let s2 := StackTransfer.after 0 28 s1
  let s3 := put s2 28 (KS.W01.frame (s2 28))
  have h1 := StackTransfer.spec (27 : Fin 29) 28 26 (by decide) (by decide) (by decide) s h26
  have h2 := StackTransfer.spec (0 : Fin 29) 28 26 (by decide) (by decide) (by decide) s1
    (by simp [s1, StackTransfer.after, h26])
  have h3 := frame_spec s2 (by simp [s2, s1, StackTransfer.after, h4])
    (by simp [s2, s1, StackTransfer.after, h26])
  have h4' := append_spec s3
  have h := ((h1.compose h2).compose h3).compose h4'
  convert h using 1 <;> (try rfl)
  · funext j
    fin_cases j <;> simp [s1, s2, s3, put, StackTransfer.after, h0, h27, h28,
      FixedDot.pairWire, FixedDot.pairPayload]
  · simp [pairTicks, s1, s2, s3, StackTransfer.after, put, h0, h27, h28]

theorem body_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) (out : List Bool) :
    RunSpec body (boundary M x i (p :: xs) p.1.val out)
      (boundary M x i xs (p.1.val + 1)
        ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ out))
      (bodyTicks M b i p) := by
  let s := put (put (boundary M x i xs p.1.val out) 27 (KS.W01.encodeRat p.2))
    0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i p.1))
  let t := put (put (put s 0 []) 27 []) 25
    ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ s 25)
  have h1 := collect_spec M b hnum hden x i p xs out
  have h2 := pair_spec s (KS.W07.DenseRatMatrix.decode M i p.1) p.2 rfl rfl rfl rfl rfl
  have h3 := increment_spec t p.1.val rfl rfl rfl
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [t, s, put, boundary, state]

end KS.W12.RowDot

end OAI
