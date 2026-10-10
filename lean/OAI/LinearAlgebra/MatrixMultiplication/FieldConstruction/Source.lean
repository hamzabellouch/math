import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.FieldCW
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.Witness
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialRestriction
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AllFieldSource

abbrev Word (K N : ℕ) := Fin (8 * K * N) → Fin 7

abbrev Index (Copies : Type*) (K N : ℕ) := Copies × Word K N

def tensor (F Copies : Type*) [CommRing F] [DecidableEq Copies] (K N : ℕ) :
    Tensor F (Index Copies K N) (Index Copies K N) (Index Copies K N) :=
  Tensor.directSum (fun _ : Copies => Tensor.power (FieldCW.tensor F 5) (8 * K * N))

def rankBudget (Copies : Type*) [Fintype Copies] (K N : ℕ) : ℕ :=
  Fintype.card Copies * ((3 * (8 * K * N) + 1) ^ 2 * 7 ^ (8 * K * N))

theorem rank_bound (F Copies : Type*) [Field F]
    [Fintype Copies] [DecidableEq Copies] (K N : ℕ) :
    Tensor.RankAtMost (tensor F Copies K N) (rankBudget Copies K N) := by
  have h := (Tensor.diagonal_rankAtMost (K := F) Copies).product
    (FieldCW.rank_power F 5 (8 * K * N))
  convert h using 1
  funext x y z
  simp [tensor, Tensor.directSum, Tensor.product, Tensor.diagonal, ite_mul]
  rfl

theorem rankBudget_pos (Copies : Type*) [Fintype Copies] (K N : ℕ)
    (hcopies : 0 < Fintype.card Copies) : 0 < rankBudget Copies K N := by
  unfold rankBudget
  exact Nat.mul_pos hcopies
    (Nat.mul_pos (pow_pos (Nat.succ_pos _) _) (pow_pos (by decide) _))

theorem rankBudget_prod (Slots Copies : Type*) [Fintype Slots] [Fintype Copies]
    (K N : ℕ) :
    rankBudget (Slots × Copies) K N = Fintype.card Slots * rankBudget Copies K N := by
  simp only [rankBudget, Fintype.card_prod, Nat.mul_assoc]

def matrixTarget (F : Type*) [CommSemiring F] (a b c L : ℕ) :=
  Tensor.directSum (fun _ : Fin L =>
    Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin c))

section Consumer

variable {F Copies : Type*} [Field F] [Fintype Copies] [DecidableEq Copies]
variable {K N a b c L : ℕ}

theorem restricted_rank_bound
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z) :
    Tensor.RankAtMost (matrixTarget F a b c L) (rankBudget Copies K N) := by
  have heq : Tensor.restrict A B C (tensor F Copies K N) = matrixTarget F a b c L :=
    funext fun x => funext fun y => funext fun z => hcoeff x y z
  rw [← heq]
  exact (rank_bound F Copies K N).restrict A B C

def restrictedApproximation
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z) :
    Tensor.PolynomialApproximation (matrixTarget F a b c L) (rankBudget Copies K N) 0 0 :=
  Tensor.PolynomialApproximation.ofRankAtMost _ _ (restricted_rank_bound A B C hcoeff)

def ofRestriction
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z)
    (hcopies : 0 < Fintype.card Copies) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hL : 0 < L) : AllFieldWitness F where
  rows := a
  inner := b
  columns := c
  multiplicity := L
  rankBound := rankBudget Copies K N
  order := 0
  degree := 0
  rows_pos := ha
  inner_pos := hb
  columns_pos := hc
  multiplicity_pos := hL
  rankBound_pos := rankBudget_pos Copies K N hcopies
  approximation := restrictedApproximation A B C hcoeff

theorem ofRestriction_polynomial
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z)
    (hcopies : 0 < Fintype.card Copies) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hL : 0 < L) :
    (ofRestriction A B C hcoeff hcopies ha hb hc hL).approximation.polynomial =
      fun x y z => Polynomial.C (matrixTarget F a b c L x y z) := rfl

end Consumer

end MatrixMultiplication.AllFieldSource

end

end OAI
