import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStateDegree
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkPortSums

namespace OAI

/-! The repeated fork state carries the original ordinary-spin Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Classical
namespace QMAForkState
variable {n c : ℕ} {d : Fin c → ℕ} {ν : Type*} [Fintype ν]
variable (G : QMAForkState n c d ν)

def matrix (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ) (constant : ℝ) :=
  qmaExchangeMatrix G.fullLeft G.fullRight (Sum.elim w J) constant

def retainedLeft : ν ⊕ QMAForkRemainder d → Fin n :=
  Sum.elim G.left (fun p => G.ports.center p.1)
def retainedRight : ν ⊕ QMAForkRemainder d → Fin n :=
  Sum.elim G.right (fun p => G.ports.port (qmaForkRemainingPort d p))
def retainedWeight (_G : QMAForkState n c d ν) (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ) :
    ν ⊕ QMAForkRemainder d → ℝ :=
  Sum.elim w (fun p => J (qmaForkRemainingPort d p))

def pairWeight (J : (Σ i, Fin (d i)) → ℝ) (b : Fin 2) (e : Fin G.ports.pairCount) : ℝ :=
  J (qmaForkPairedPort d (G.ports.pairEquiv.symm e,b))

theorem retained_distinct (e : ν ⊕ QMAForkRemainder d) :
    G.retainedLeft e ≠ G.retainedRight e := by
  rcases e with e | p
  · exact G.distinct e
  · exact G.ports.center_ne_port p.1 _

theorem matrix_pair_split (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ) (constant : ℝ) :
    G.matrix w J constant =
      qmaExchangeMatrix G.retainedLeft G.retainedRight (G.retainedWeight w J) constant +
      ∑ e, (((G.pairWeight J 0 e : ℝ):ℂ) •
        sourceHeisenbergMatrix n (G.ports.site e 0) (G.ports.site e 1) +
        ((G.pairWeight J 1 e : ℝ):ℂ) •
        sourceHeisenbergMatrix n (G.ports.site e 0) (G.ports.site e 2)) := by
  have hs := G.ports.all_port_sum (fun p => (J p : ℂ) •
    sourceHeisenbergMatrix n (G.ports.center p.1) (G.ports.port p))
  simp only [Fin.sum_univ_two] at hs
  change (∑ p, (J p : ℂ) • sourceHeisenbergMatrix n (G.ports.center p.1) (G.ports.port p)) =
    (∑ e, (((G.pairWeight J 0 e : ℝ):ℂ) •
        sourceHeisenbergMatrix n (G.ports.site e 0) (G.ports.site e 1) +
      ((G.pairWeight J 1 e : ℝ):ℂ) •
        sourceHeisenbergMatrix n (G.ports.site e 0) (G.ports.site e 2))) +
    ∑ p, (J (qmaForkRemainingPort d p) : ℂ) • sourceHeisenbergMatrix n
      (G.ports.center p.1) (G.ports.port (qmaForkRemainingPort d p)) at hs
  simp only [matrix,qmaExchangeMatrix,fullLeft,fullRight,retainedLeft,retainedRight,
    retainedWeight,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rw [hs]
  abel

def nextWeight (R : ℝ) (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ) : G.NextEdge → ℝ
  | .inl (.inl e) => w e
  | .inl (.inr e) => 2*G.pairWeight J 0 e*G.pairWeight J 1 e
  | .inr (.inl _) => R^2
  | .inr (.inr (e,b)) => 2*R*G.pairWeight J b e

def nextActive (R : ℝ) (J : (Σ i, Fin (d i)) → ℝ)
    (p : Σ i, Fin (d i / 2 + d i % 2)) : ℝ :=
  match G.ports.nextPortEquiv p with
  | .inl _ => R
  | .inr p => J (qmaForkRemainingPort d p)

def nextConstant (R constant : ℝ) (J : (Σ i, Fin (d i)) → ℝ) : ℝ :=
  (constant + ∑ e, qmaForkOffset (G.pairWeight J 0 e) (G.pairWeight J 1 e)) +
    3*(G.ports.pairCount : ℝ)*R^2

end QMAForkState
end ContinuumCoulomb

end

end OAI
