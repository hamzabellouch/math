import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkDegrees
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkGraph

namespace OAI

/-! The degree-counted fork star is the actual ordinary-spin gadget graph. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical

def qmaForkOldEquiv (d : ℕ) : Unit ⊕ Fin d ≃ Fin (1+d) :=
  (Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1)) (Equiv.refl _)).trans finSumFinEquiv

def qmaForkCenter (d : ℕ) : Fin (1+d) := qmaForkOldEquiv d (.inl ())
def qmaForkPort (d : ℕ) (j : Fin d) : Fin (1+d) := qmaForkOldEquiv d (.inr j)

def qmaForkStarEmbedding (d : ℕ) : QMAForkStarVertex d ≃ Fin ((1+d)+(d/2)*2) :=
  (((Equiv.sumAssoc Unit (Fin d) (Fin (d/2) × Fin 2)).symm).trans
    (Equiv.sumCongr (qmaForkOldEquiv d) (Equiv.refl _))).trans (vertexEquiv (1+d) (d/2))

@[simp] theorem qmaForkStarEmbedding_center (d : ℕ) :
    qmaForkStarEmbedding d (.inl ()) = old (1+d) (d/2) (qmaForkCenter d) := rfl
@[simp] theorem qmaForkStarEmbedding_port (d : ℕ) (j : Fin d) :
    qmaForkStarEmbedding d (.inr (.inl j)) = old (1+d) (d/2) (qmaForkPort d j) := rfl
@[simp] theorem qmaForkStarEmbedding_new (d : ℕ) (i : Fin (d/2)) (b : Fin 2) :
    qmaForkStarEmbedding d (.inr (.inr (i,b))) = fresh (1+d) (d/2) i b := rfl

def qmaForkStarSite (d : ℕ) (i : Fin (d/2)) : Fin 3 → Fin (1+d) :=
  ![qmaForkCenter d,qmaForkPort d (qmaForkPortEquiv d (.inl (i,0))),
    qmaForkPort d (qmaForkPortEquiv d (.inl (i,1)))]

theorem qmaForkStarSite_injective (d : ℕ) (i : Fin (d/2)) :
    Function.Injective (qmaForkStarSite d i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [qmaForkStarSite,qmaForkCenter,qmaForkPort] at h ⊢

theorem qmaForkStar_degree_transport (d : ℕ) (v : QMAForkStarVertex d) :
    (∑ e, if qmaForkStarEmbedding d (qmaForkStarLeft d e) = qmaForkStarEmbedding d v ∨
      qmaForkStarEmbedding d (qmaForkStarRight d e) = qmaForkStarEmbedding d v then 1 else 0) =
      qmaForkStarDegree d v := by
  simp only [Equiv.apply_eq_iff_eq,qmaForkStarDegree]

def qmaForkStarWeight (d : ℕ) (R : ℝ) (J : Fin d → ℝ) : QMAForkStarEdge d → ℝ
  | .inl _ => R^2
  | .inr (.inl _) => R
  | .inr (.inr (.inl p)) => 2*R*J (qmaForkPortEquiv d (.inl p))
  | .inr (.inr (.inr (.inl i))) =>
      2*J (qmaForkPortEquiv d (.inl (i,0)))*J (qmaForkPortEquiv d (.inl (i,1)))
  | .inr (.inr (.inr (.inr k))) => J (qmaForkPortEquiv d (.inr k))

def qmaForkStarOffset (d : ℕ) (constant R : ℝ) (J : Fin d → ℝ) : ℝ :=
  (constant+∑ i, qmaForkOffset (J (qmaForkPortEquiv d (.inl (i,0))))
    (J (qmaForkPortEquiv d (.inl (i,1)))))+3*((d/2:ℕ):ℝ)*(R^2)

theorem qmaForkStar_matrix (d : ℕ) (constant R : ℝ) (J : Fin d → ℝ) :
    qmaExchangeMatrix (fun e => qmaForkStarEmbedding d (qmaForkStarLeft d e))
      (fun e => qmaForkStarEmbedding d (qmaForkStarRight d e)) (qmaForkStarWeight d R J)
      (qmaForkStarOffset d constant R J) =
    qmaForksGraph (fun _ : Fin (d%2) => qmaForkCenter d)
      (fun k => qmaForkPort d (qmaForkPortEquiv d (.inr k)))
      (fun k => J (qmaForkPortEquiv d (.inr k))) constant R (qmaForkStarSite d)
      (fun i => J (qmaForkPortEquiv d (.inl (i,0))))
      (fun i => J (qmaForkPortEquiv d (.inl (i,1)))) := by
  simp only [qmaForksGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_two,Fin.sum_univ_three,qmaForkStarLeft,qmaForkStarRight,qmaForkStarWeight,qmaForkStarOffset,
    qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,qmaForksBaseLeft,
    qmaForksBaseRight,qmaForksBaseWeight,Sum.elim_inl,Sum.elim_inr,qmaForkMember,qmaForkAmplitude,
    qmaForkStarSite,Matrix.cons_val_zero,
    qmaForkStarEmbedding_center,qmaForkStarEmbedding_port,qmaForkStarEmbedding_new,
    Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow,Finset.sum_add_distrib]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_pow,Complex.ofReal_add,add_smul]
  push_cast
  abel

end ContinuumCoulomb

end

end OAI
