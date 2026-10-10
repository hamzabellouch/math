import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkCalibration

namespace OAI

/-! Explicit ordinary-spin graph for an entire parallel singlet-routing layer. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

def qmaParallelGraphLeft {n r : ℕ} (base : ν → Fin n) (site : Fin r → κ → Fin n) :
    ν ⊕ (Fin r ⊕ (Fin r × κ)) → Fin (n+r*2)
  | .inl a => old n r (base a)
  | .inr (.inl e) => fresh n r e 0
  | .inr (.inr p) => old n r (site p.1 p.2)

def qmaParallelGraphRight {n r : ℕ} (base : ν → Fin n) (member : Fin r → κ → Fin 2) :
    ν ⊕ (Fin r ⊕ (Fin r × κ)) → Fin (n+r*2)
  | .inl a => old n r (base a)
  | .inr (.inl e) => fresh n r e 1
  | .inr (.inr p) => fresh n r p.1 (member p.1 p.2)

def qmaParallelGraphWeight {r : ℕ} (base : ν → ℝ) (Delta : ℝ) (amplitude : Fin r → κ → ℝ) :
    ν ⊕ (Fin r ⊕ (Fin r × κ)) → ℝ
  | .inl a => base a
  | .inr (.inl _) => Delta
  | .inr (.inr p) => amplitude p.1 p.2

omit [Fintype ν] [Fintype κ] in
theorem qmaParallelGraph_distinct {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) :
    ∀ a, qmaParallelGraphLeft left site a ≠ qmaParallelGraphRight right member a := by
  intro a
  rcases a with a | a
  · exact fun h => hneq a (old_injective n r h)
  rcases a with e | p
  · intro h
    have hh := congrArg Prod.snd (fresh_injective n r (a₁ := (e,0)) (a₂ := (e,1)) h)
    norm_num at hh
  · exact old_ne_fresh n r _ _ _

def qmaPhysicalParallelHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ physicalMediatorPenalty r Delta +
    (C ⊗ₖ 1 + ∑ e, qmaPhysicalSingletStar n r e (site e) (member e) (amplitude e))

theorem qmaParallelGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant Delta : ℝ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    (qmaExchangeMatrix (qmaParallelGraphLeft left site) (qmaParallelGraphRight right member)
      (qmaParallelGraphWeight weight Delta amplitude) (constant+3*r*Delta)).submatrix
        (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r Delta (qmaExchangeMatrix left right weight constant)
        site member amplitude := by
  simp only [qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    submatrix_add_apply,submatrix_sum,submatrix_smul_apply,
    Matrix.submatrix_one_equiv,heisenberg_old n r _ _ (hneq _),heisenberg_central,
    heisenberg_spoke]
  unfold qmaPhysicalParallelHamiltonian qmaPhysicalSingletStar
  rw [physicalMediatorPenalty_offset]
  simp only [Matrix.add_kronecker,Matrix.kronecker_add,Matrix.smul_kronecker,
    Matrix.kronecker_smul,Matrix.one_kronecker_one,sum_kronecker,kronecker_sum,
    Complex.ofReal_add,add_smul,Finset.smul_sum]
  abel

theorem qmaPhysicalParallel_transform (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      qmaPhysicalParallelHamiltonian n r Delta C site member amplitude *
        fullMediatorBellMatrix n r =
      routingHamiltonian n r Delta C (qmaRoutingStars n r site member amplitude) := by
  simp only [qmaPhysicalParallelHamiltonian,routingHamiltonian,qmaRoutingStars,mul_add,
    add_mul,Finset.mul_sum,Finset.sum_mul,physicalMediatorPenalty_full_transform,
    liftedSource_full_transform,qmaPhysicalSingletStar_transform]

theorem qmaPhysicalParallel_bottom (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    mediatorFullBottom n r (qmaPhysicalParallelHamiltonian n r Delta C site member amplitude) =
      mediatorFullBottom n r (routingHamiltonian n r Delta C (qmaRoutingStars n r site member amplitude)) := by
  have h := mediatorFullBottom_unitary n r (fullMediatorBellMatrix n r)
    (qmaPhysicalParallelHamiltonian n r Delta C site member amplitude)
    (fullMediatorBellMatrix_gram n r) (fullMediatorBellMatrix_cogram n r)
  rw [qmaPhysicalParallel_transform] at h
  exact h.symm

end ContinuumCoulomb

end

end OAI
