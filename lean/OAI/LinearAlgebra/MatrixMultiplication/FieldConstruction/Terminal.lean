import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FiniteFamily
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.TerminalRelabel

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldTerminal

open MatrixMultiplication.Foundation AllFieldFiniteFamily CommonDimensions
open scoped BigOperators Classical

variable {F : Type*} {H : Type} [Field F] [Fintype H]
  {X Y Z : H → Type} [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
  (T : ∀ h, Tensor F (X h) (Y h) (Z h)) (A B C : H → Type)
  [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
  (maps : ∀ h, LocalMap (T h) (Tensor.matrixCoefficients (A h) (B h) (C h)))

def terminalProductMap :
    LocalMap (familyProduct T) (Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h)) :=
  LocalMap.ofExists (TerminalProducts.matrix_restriction_of_history_restrictions
    T A B C (fun h => (maps h).x) (fun h => (maps h).y) (fun h => (maps h).z)
    (fun h => (maps h).coefficient))

variable {I : Type} [Fintype I] {K N : ℕ}

def terminalExecution
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T))) :
    Execution (cwSource F K N)
      (AllFieldSource.matrixTarget F (Fintype.card (∀ h, A h))
        (Fintype.card (∀ h, B h)) (Fintype.card (∀ h, C h)) (Fintype.card I)) :=
  (E.restrict _ ((terminalProductMap T A B C maps).parallelCopies I)).restrict _
    (LocalMap.ofExists (TerminalRelabel.directSum_matrix_restrict_fin (K := F)
      I (∀ h, A h) (∀ h, B h) (∀ h, C h)))

@[simp] theorem terminalExecution_copies
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T))) :
    Fintype.card (terminalExecution T A B C maps E).Copies = Fintype.card E.Copies := rfl

def finish
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) : AllFieldWitness F :=
  (terminalExecution T A B C maps E).toWitness hA hB hC hI

@[simp] theorem finish_multiplicity
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).multiplicity = Fintype.card I := rfl

theorem finish_volume
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).volume =
      ∏ h, Fintype.card (A h) * Fintype.card (B h) * Fintype.card (C h) := by
  change Fintype.card (∀ h, A h) * Fintype.card (∀ h, B h) *
    Fintype.card (∀ h, C h) = _
  simp only [Fintype.card_pi, Finset.prod_mul_distrib]

@[simp] theorem finish_rankBound
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).rankBound =
      AllFieldSource.rankBudget E.Copies K N := rfl

end MatrixMultiplication.AllFieldTerminal

end

end OAI
