import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.BinaryEncoding

namespace OAI

section

namespace KS.W12.FixedDot

open scoped BigOperators

def pairPayload (p : ℚ × ℚ) : List Bool := KS.W01.encodeRat p.1 ++ KS.W01.encodeRat p.2

def pairWire (p : ℚ × ℚ) : List Bool := KS.W01.frame (pairPayload p)

def inputWire (ps : List (ℚ × ℚ)) : List Bool := ps.flatMap pairWire

def dotValue (ps : List (ℚ × ℚ)) : ℚ := (ps.map (fun p => p.1 * p.2)).sum

@[simp] theorem inputWire_nil : inputWire [] = [] := rfl
@[simp] theorem inputWire_cons (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    inputWire (p :: ps) = pairWire p ++ inputWire ps := rfl

@[simp] theorem dotValue_nil : dotValue [] = 0 := rfl
@[simp] theorem dotValue_cons (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    dotValue (p :: ps) = p.1 * p.2 + dotValue ps := rfl

theorem unframe_inputWire_cons (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    KS.W01.unframe (inputWire (p :: ps)) = some (pairPayload p, inputWire ps) :=
  KS.W01.unframe_frame_append _ _

theorem read_pairPayload (p : ℚ × ℚ) :
    KS.W01.readRat (pairPayload p) = some (p.1, KS.W01.encodeRat p.2) :=
  KS.W01.readRat_encode_append _ _

@[simp] theorem pairWire_length (p : ℚ × ℚ) :
    (pairWire p).length = 2 * (pairPayload p).length + 1 := KS.W01.length_frame _

theorem pairWire_nonempty (p : ℚ × ℚ) : pairWire p ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [pairWire_length, List.length_nil] at hl
  omega

theorem inputWire_cons_nonempty (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    inputWire (p :: ps) ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [inputWire_cons, List.length_append, pairWire_length, List.length_nil] at hl
  omega

theorem dotValue_ofFn {n : ℕ} (x y : Fin n → ℚ) :
    dotValue (List.ofFn (fun i => (x i, y i))) = ∑ i, x i * y i := by
  simp [dotValue, List.sum_ofFn]

theorem accumulator_step (a : ℚ) (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    (a + p.1 * p.2) + dotValue ps = a + dotValue (p :: ps) := by
  rw [dotValue_cons, add_assoc]

end KS.W12.FixedDot

end

end OAI
