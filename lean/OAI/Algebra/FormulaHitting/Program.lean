import OAI.Algebra.FormulaHitting.Generator
import OAI.Algebra.FormulaHitting.BitModel

namespace OAI

namespace NCHitting

open BitModel

def dimensionExpr (nRegister sRegister : ℕ) : Expr :=
  .mul (.mul (.literal 2) (.read nRegister)) (.power (.read sRegister) (.literal 2))

def entryProgram : Program :=
  .branch (.less (.read 0) (.read 1))
    (.emit (.odd (.sub (.sub (.read 1) (.read 0)) (.literal 1)))
      (.literal 1)
      (.mul (.read 1) (.power (.add (.read 2) (.literal 1))
        (.sub (.read 1) (.read 0)))))
    (.emit (.literal 0) (.literal 0) (.literal 1))

def rowProgram : Program := .loop (dimensionExpr 2 3) entryProgram

def variableProgram : Program := .loop (dimensionExpr 1 2) rowProgram

def generatorProgram : Program :=
  .branch (.mul (.equal (.read 0) (.literal 1)) (.equal (.read 1) (.literal 1)))
    (.emit (.literal 0) (.literal 1) (.literal 1))
    (.loop (.read 0) variableProgram)

def encodedEntry (i r q : ℕ) : BitModel.RationalCode :=
  if q < r then ⟨decide ((r-q-1) % 2 = 1), 1, r * (i+1)^(r-q)⟩
  else ⟨false, 0, 1⟩

def encodedOutput (n s : ℕ) : List BitModel.RationalCode :=
  if n = 1 ∧ s = 1 then [⟨false, 1, 1⟩]
  else (List.range n).flatMap fun i =>
    (List.range (2*n*s^2)).flatMap fun r =>
      (List.range (2*n*s^2)).map fun q => encodedEntry i r q

def generate (n s : ℕ) : ProgramResult := BitModel.execute generatorProgram [n, s]

theorem entryProgram_output (n s i r q : ℕ) :
    (entryProgram.run [q,r,i,n,s]).output = [encodedEntry i r q] := by
  by_cases h : q < r <;>
    simp [entryProgram, Program.run, Expr.run, encodedEntry, h]

theorem rowProgram_output (n s i r : ℕ) :
    (rowProgram.run [r,i,n,s]).output =
      (List.range (2*n*s^2)).map (encodedEntry i r) := by
  simp [rowProgram, Program.run, dimensionExpr, Expr.run, List.flatMap_map,
    entryProgram_output, ← List.map_eq_flatMap]

theorem variableProgram_output (n s i : ℕ) :
    (variableProgram.run [i,n,s]).output =
      (List.range (2*n*s^2)).flatMap fun r =>
        (List.range (2*n*s^2)).map (encodedEntry i r) := by
  simp [variableProgram, Program.run, dimensionExpr, Expr.run, List.flatMap_map,
    rowProgram_output]

theorem generate_output (n s : ℕ) : (generate n s).output = encodedOutput n s := by
  by_cases hn : n = 1 <;> by_cases hs : s = 1 <;>
    simp [generate, BitModel.execute, generatorProgram, Program.run, Expr.run,
      hn, hs, List.flatMap_map, variableProgram_output, encodedOutput]

theorem encodedEntry_denominator_pos (i r q : ℕ) :
    0 < (encodedEntry i r q).denominator := by
  unfold encodedEntry
  split_ifs with h
  · simp only
    apply Nat.mul_pos (by omega)
    exact pow_pos (by omega) _
  · decide

def decode (entry : BitModel.RationalCode) : ℚ :=
  (if entry.negative then -(entry.numerator : ℚ) else entry.numerator) / entry.denominator

theorem decode_encodedEntry (i r q : ℕ) :
    decode (encodedEntry i r q) = matrixEntry (i+1) r q := by
  by_cases h : q < r
  · simp only [encodedEntry, ite_eq_left h, decode, matrixEntry]
    rw [neg_one_pow_eq_pow_mod_two]
    by_cases hm : (r-q-1) % 2 = 1
    · simp [hm, Nat.cast_mul, Nat.cast_pow]
    · have hz : (r-q-1) % 2 = 0 := by omega
      simp [hz, Nat.cast_mul, Nat.cast_pow]
  · simp [encodedEntry, decode, matrixEntry, h]

theorem encodedEntry_bits_le {n d i r q : ℕ} (hi : i < n) (hr : r < d) :
    (encodedEntry i r q).bits ≤ 4 + entryBitBound n d := by
  unfold encodedEntry
  split_ifs with h
  · have hb := denominator_size_le (i := i+1) (q := q) (show i+1 ≤ n by omega) hr
    simp only [BitModel.RationalCode.bits, BitModel.width, Nat.size_one]
    omega
  · simp only [BitModel.RationalCode.bits, BitModel.width, Nat.size_one, Nat.size_zero]
    unfold entryBitBound
    omega

end NCHitting

end OAI
