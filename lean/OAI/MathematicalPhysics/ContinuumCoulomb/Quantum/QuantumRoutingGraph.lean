import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingPhysical
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeRounding
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorGraph

namespace OAI

/-! Explicit ordinary-spin edges for a routing star, with the central offset. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

def qmaStarGraphLeft {n r : ℕ} (base : ν → Fin n) (_e : Fin r) (site : κ → Fin n) :
    ν ⊕ (Fin r ⊕ κ) → Fin (n+r*2)
  | .inl a => old n r (base a)
  | .inr (.inl f) => fresh n r f 0
  | .inr (.inr a) => old n r (site a)

def qmaStarGraphRight {n r : ℕ} (base : ν → Fin n) (e : Fin r) (member : κ → Fin 2) :
    ν ⊕ (Fin r ⊕ κ) → Fin (n+r*2)
  | .inl a => old n r (base a)
  | .inr (.inl f) => fresh n r f 1
  | .inr (.inr a) => fresh n r e (member a)

def qmaStarGraphWeight {r : ℕ} (base : ν → ℝ) (Delta : ℝ) (amplitude : κ → ℝ) :
    ν ⊕ (Fin r ⊕ κ) → ℝ
  | .inl a => base a
  | .inr (.inl _) => Delta
  | .inr (.inr a) => amplitude a

omit [Fintype ν] [Fintype κ] in
theorem qmaStarGraph_distinct {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (e : Fin r) (site : κ → Fin n) (member : κ → Fin 2) :
    ∀ a, qmaStarGraphLeft left e site a ≠ qmaStarGraphRight right e member a := by
  intro a
  rcases a with a | a
  · exact fun h => hneq a (old_injective n r h)
  · rcases a with f | a
    · intro h
      have hf := congrArg Prod.snd (fresh_injective n r (a₁ := (f,0)) (a₂ := (f,1)) h)
      norm_num at hf
    · exact old_ne_fresh n r _ _ _

theorem qmaStarGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant Delta : ℝ)
    (e : Fin r) (site : κ → Fin n) (member : κ → Fin 2) (amplitude : κ → ℝ) :
    (qmaExchangeMatrix (qmaStarGraphLeft left e site) (qmaStarGraphRight right e member)
      (qmaStarGraphWeight weight Delta amplitude) (constant+3*r*Delta)).submatrix
        (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalRoutingHamiltonian n r Delta (qmaExchangeMatrix left right weight constant)
        e site member amplitude := by
  simp only [qmaExchangeMatrix,Fintype.sum_sum_type,qmaStarGraphLeft,qmaStarGraphRight,
    qmaStarGraphWeight,submatrix_add_apply,submatrix_sum,submatrix_smul_apply,
    Matrix.submatrix_one_equiv,heisenberg_old n r _ _ (hneq _),heisenberg_central,
    heisenberg_spoke]
  unfold qmaPhysicalRoutingHamiltonian qmaPhysicalSingletStar
  rw [physicalMediatorPenalty_offset]
  simp only [Matrix.add_kronecker,Matrix.kronecker_add,Matrix.smul_kronecker,
    Matrix.kronecker_smul,Matrix.one_kronecker_one,sum_kronecker,kronecker_sum,
    Complex.ofReal_add,add_smul,Finset.smul_sum]
  abel

theorem qmaExchangeMatrix_lift {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ) :
    (qmaExchangeMatrix (fun a => old n r (left a)) (fun a => old n r (right a))
      weight constant).submatrix (basisEquiv n r) (basisEquiv n r) =
        qmaExchangeMatrix left right weight constant ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  simp only [qmaExchangeMatrix,submatrix_add_apply,submatrix_sum,submatrix_smul_apply,
    Matrix.submatrix_one_equiv,heisenberg_old n r _ _ (hneq _),Matrix.add_kronecker,
    Matrix.smul_kronecker,Matrix.one_kronecker_one,sum_kronecker]

theorem qmaExchangeMatrix_lift_norm {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ) :
    ‖spinMatrixOperator (qmaExchangeMatrix left right weight constant ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤
      3*(∑ a, |weight a|)+|constant| := by
  rw [← qmaExchangeMatrix_lift left right hneq weight constant,reindex_operator_norm]
  exact qmaExchangeMatrix_norm _ _ (fun a h => hneq a (old_injective n r h)) weight constant

end ContinuumCoulomb

end

end OAI
