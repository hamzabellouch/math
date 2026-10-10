import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.TerminalRelabel

variable {K I A B C I' A' B' C' : Type*} [CommSemiring K]

def taggedPair (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) :
    I' × (A' × B') → I × (A × B) :=
  fun x => (eI x.1, (eA x.2.1, eB x.2.2))

theorem directSum_matrix_pullback
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    Tensor.pullback (taggedPair eI eA eB) (taggedPair eI eB eC) (taggedPair eI eC eA)
      (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
        Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') := by
  funext x y z
  simp only [Tensor.pullback, taggedPair, Tensor.directSum, Tensor.matrixCoefficients,
    eI.injective.eq_iff, eA.injective.eq_iff, eB.injective.eq_iff, eC.injective.eq_iff]

theorem directSum_matrix_restrict_equiv
    [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    Tensor.restrict
      (fun x s => if s = taggedPair eI eA eB x then (1 : K) else 0)
      (fun y s => if s = taggedPair eI eB eC y then (1 : K) else 0)
      (fun z s => if s = taggedPair eI eC eA z then (1 : K) else 0)
      (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
        Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') := by
  rw [← Tensor.pullback_eq_restrict]
  exact directSum_matrix_pullback eI eA eB eC

theorem exists_directSum_matrix_restrict_equiv
    [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    ∃ (a : (I' × (A' × B')) → (I × (A × B)) → K)
      (b : (I' × (B' × C')) → (I × (B × C)) → K)
      (c : (I' × (C' × A')) → (I × (C × A)) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') :=
  ⟨_, _, _, directSum_matrix_restrict_equiv eI eA eB eC⟩

theorem directSum_matrix_restrict_of_card_eq
    (I A B C : Type*) [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {L a b c : ℕ} (hI : Fintype.card I = L) (hA : Fintype.card A = a)
    (hB : Fintype.card B = b) (hC : Fintype.card C = c) :
    ∃ (aa : (Fin L × (Fin a × Fin b)) → (I × (A × B)) → K)
      (bb : (Fin L × (Fin b × Fin c)) → (I × (B × C)) → K)
      (cc : (Fin L × (Fin c × Fin a)) → (I × (C × A)) → K),
      Tensor.restrict aa bb cc
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : Fin L =>
            Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) :=
  exists_directSum_matrix_restrict_equiv
    (Fintype.equivFinOfCardEq hI).symm (Fintype.equivFinOfCardEq hA).symm
    (Fintype.equivFinOfCardEq hB).symm (Fintype.equivFinOfCardEq hC).symm

theorem directSum_matrix_restrict_fin
    (I A B C : Type*) [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    ∃ (a : (Fin (Fintype.card I) × (Fin (Fintype.card A) × Fin (Fintype.card B))) →
        (I × (A × B)) → K)
      (b : (Fin (Fintype.card I) × (Fin (Fintype.card B) × Fin (Fintype.card C))) →
        (I × (B × C)) → K)
      (c : (Fin (Fintype.card I) × (Fin (Fintype.card C) × Fin (Fintype.card A))) →
        (I × (C × A)) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : Fin (Fintype.card I) =>
            Tensor.matrixCoefficients (K := K)
              (Fin (Fintype.card A)) (Fin (Fintype.card B)) (Fin (Fintype.card C))) :=
  directSum_matrix_restrict_of_card_eq I A B C rfl rfl rfl rfl

end MatrixMultiplication.TerminalRelabel

end

end OAI
