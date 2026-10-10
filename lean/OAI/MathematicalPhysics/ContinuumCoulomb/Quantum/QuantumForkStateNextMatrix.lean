import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStateMatrix

namespace OAI

/-! The active-star transition is exactly the calibrated parallel fork Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Classical
namespace QMAForkState
variable {n c : ℕ} {d : Fin c → ℕ} {ν : Type*} [Fintype ν]
variable (G : QMAForkState n c d ν)

theorem matrix_expand (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ) (constant : ℝ) :
    G.matrix w J constant =
      ((∑ e, (w e:ℂ) • sourceHeisenbergMatrix n (G.left e) (G.right e)) +
        ∑ p, (J p:ℂ) • sourceHeisenbergMatrix n (G.ports.center p.1) (G.ports.port p)) +
      (constant:ℂ) • 1 := by
  simp only [matrix,qmaExchangeMatrix,fullLeft,fullRight,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr]

theorem next_active_sum (R : ℝ) (J : (Σ i, Fin (d i)) → ℝ) :
    (∑ p, (G.nextActive R J p:ℂ) • sourceHeisenbergMatrix (n+G.ports.pairCount*2)
      (G.next.ports.center p.1) (G.next.ports.port p)) =
    (∑ e, (R:ℂ) • sourceHeisenbergMatrix (n+G.ports.pairCount*2)
      (old n G.ports.pairCount (G.ports.site e 0)) (fresh n G.ports.pairCount e 0)) +
    ∑ p : QMAForkRemainder d, (J (qmaForkRemainingPort d p):ℂ) •
      sourceHeisenbergMatrix (n+G.ports.pairCount*2)
        (old n G.ports.pairCount (G.ports.center p.1))
        (old n G.ports.pairCount (G.ports.port (qmaForkRemainingPort d p))) := by
  rw [G.ports.next_port_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    simp only [nextActive,next,QMAForkPorts.next,Function.comp_apply,
      Equiv.apply_symm_apply,QMAForkPorts.nextPortAux]
    rfl
  · apply Finset.sum_congr rfl
    intro p _
    simp only [nextActive,next,QMAForkPorts.next,Function.comp_apply,
      Equiv.apply_symm_apply,QMAForkPorts.nextPortAux]
    rfl

theorem next_matrix_is_forks (R : ℝ) (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ)
    (constant : ℝ) :
    G.next.matrix (G.nextWeight R w J) (G.nextActive R J) (G.nextConstant R constant J) =
      qmaForksGraph G.retainedLeft G.retainedRight (G.retainedWeight w J) constant R
        G.ports.site (G.pairWeight J 0) (G.pairWeight J 1) := by
  rw [matrix_expand,G.next_active_sum]
  simp only [qmaForksGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_two,Fin.sum_univ_three,next,qmaForkBackgroundLeft,qmaForkBackgroundRight,
    qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    qmaForksBaseLeft,qmaForksBaseRight,qmaForksBaseWeight,nextWeight,nextConstant,
    retainedLeft,retainedRight,retainedWeight,Sum.elim_inl,Sum.elim_inr,
    qmaForkAmplitude,qmaForkMember,qmaForkOuter]
  simp only [ite_true,Finset.sum_add_distrib]
  ac_rfl

end QMAForkState
end ContinuumCoulomb

end

end OAI
