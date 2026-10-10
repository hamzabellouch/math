import OAI.LinearAlgebra.MatrixMultiplication.Entropy.BaseConditionalReaders

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels

abbrev Word := Script.Coord (Fin 2) Script.dual
def source : FlaggedTensor Word Word Word := Script.tensor BaseTwo.flagged Script.dual
abbrev Support := RetainedLeaf source .B .C

def readable : ReadableTensor source :=
  ReadableTensor.script BaseTwo.flagged BaseConditionalReaders.baseTwoReadable Script.dual

def program := terminationProgram source .B .C (by intro h; cases h)
  readable.program readable.context_eq readable.view_eq

theorem program_complete : program.Complete :=
  terminationProgram_complete source .B .C (by intro h; cases h)
    readable.program readable.context_eq readable.view_eq readable.complete

theorem record_injective : Function.Injective
    (labelRecordOf program.labels (1 + readable.depth)) :=
  terminationRecord_injective source .B .C (by intro h; cases h)
    readable.program readable.context_eq readable.view_eq readable.complete

def x (a : Support) : Word := a.val.val.1

theorem coord_card (U : Type*) [Fintype U] (s : Script) :
    Fintype.card (Script.Coord U s) = Fintype.card U ^ s.factors := by
  induction s with
  | base =>
    change Fintype.card U = Fintype.card U ^ 1
    exact (pow_one _).symm
  | step prior center m ih =>
    change Fintype.card (Fin m → Script.Coord U prior) = _
    simp only [Fintype.card_fun, Fintype.card_fin, ih, Script.factors, pow_mul]

theorem word_card : Fintype.card Word = 2 ^ 288 := by
  simpa only [Fintype.card_fin, Script.dual_factors] using coord_card (Fin 2) Script.dual

end MatrixMultiplication.DualWitness

end

end OAI
