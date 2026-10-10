import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkIteration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathsGraph

namespace OAI

/-! The private-port initial state is the physical odd-subdivision Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Classical

def qmaSubdivisionWeighted {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℝ) (constant R : ℝ) : QMAWeightedForkNetwork n where
  graph := qmaSubdivisionNetwork left right
  weight := fun _ => R^2
  active := fun p => qmaPathAmplitude false R (J (qmaOriginalPortEquiv left right p).1)
    (qmaOriginalPortEquiv left right p).2
  constant := (constant+∑ e, qmaPathOffset (J e))+3*(m:ℝ)*R^2

def qmaOriginalSite {n m : ℕ} (left right : Fin m → Fin n) (e : Fin m) : Fin 2 → Fin n :=
  ![left e,right e]

theorem qmaOriginalSite_injective {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (e : Fin m) : Function.Injective (qmaOriginalSite left right e) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [qmaOriginalSite] at h ⊢
  · exact (hneq e h).elim
  · exact (hneq e h.symm).elim

theorem qmaSubdivision_weighted_matrix {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℝ) (constant R : ℝ) :
    let G := qmaSubdivisionWeighted left right J constant R
    G.graph.state.matrix G.weight G.active G.constant =
      qmaPathsGraph (fun a : Fin 0 => Fin.elim0 a) (fun a : Fin 0 => Fin.elim0 a)
        (fun _ => 0) constant R (qmaOriginalSite left right) (fun _ => false) J := by
  dsimp only
  rw [QMAForkState.matrix_expand]
  have hs := (qmaOriginalPortEquiv left right).symm.sum_comp
    (fun p => (qmaPathAmplitude false R (J (qmaOriginalPortEquiv left right p).1)
      (qmaOriginalPortEquiv left right p).2 : ℂ) •
        sourceHeisenbergMatrix (n+m*2) (old n m p.1)
          (fresh n m (qmaOriginalPortEquiv left right p).1 (qmaOriginalPortEquiv left right p).2))
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type] at hs
  change (∑ e, ((R^2:ℝ):ℂ) • sourceHeisenbergMatrix (n+m*2)
    (fresh n m e 0) (fresh n m e 1)) +
    (∑ p, (qmaPathAmplitude false R (J (qmaOriginalPortEquiv left right p).1)
      (qmaOriginalPortEquiv left right p).2 : ℂ) • sourceHeisenbergMatrix (n+m*2)
        (old n m p.1) (fresh n m (qmaOriginalPortEquiv left right p).1
          (qmaOriginalPortEquiv left right p).2)) +
    (((constant+∑ e, qmaPathOffset (J e))+3*(m:ℝ)*R^2:ℝ):ℂ) • 1 = _
  rw [← hs]
  simp only [qmaPathsGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_two,qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    qmaOriginalSite,qmaPathAmplitude,qmaPathMember,Finset.univ_eq_empty,Finset.sum_empty,zero_add]
  ac_rfl

theorem qmaSubdivision_energy_error {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin m → ℝ) (constant : ℝ)
    {N : ℝ} (hN : 0 < N) :
    let A := 3*∑ e, (1+2*|J e|)
    let B := |constant|+4*∑ e, (1+|J e|)^2
    let R := qmaRoutingScale A B N
    |(qmaSubdivisionWeighted left right J constant R).energy -
      sourceMatrixBottom n (qmaExchangeMatrix left right J constant)| ≤ 1/N := by
  dsimp only
  unfold QMAWeightedForkNetwork.energy
  rw [qmaSubdivision_weighted_matrix]
  dsimp only [qmaSubdivisionWeighted,qmaSubdivisionNetwork]
  have h := qmaPathsGraph_accuracy (fun a : Fin 0 => Fin.elim0 a)
    (fun a : Fin 0 => Fin.elim0 a) (fun a => Fin.elim0 a) (fun _ => 0) constant
    (qmaOriginalSite left right) (qmaOriginalSite_injective left right hneq) (fun _ => false) J hN
  simpa [qmaExchangeMatrix,qmaOriginalSite,add_comm] using h

end ContinuumCoulomb

end

end OAI
