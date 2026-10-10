import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkPorts

namespace OAI

/-! Finite-sum identities for the paired and unpaired edges of a fork layer. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMAForkPorts
variable {n c : ℕ} {d : Fin c → ℕ} (P : QMAForkPorts n c d)
variable {M : Type*} [AddCommMonoid M]

theorem all_port_sum (f : (Σ i, Fin (d i)) → M) :
    (∑ p, f p) =
      (∑ e : Fin P.pairCount, ∑ b : Fin 2,
        f (qmaForkPairedPort d (P.pairEquiv.symm e,b))) +
      ∑ p : QMAForkRemainder d, f (qmaForkRemainingPort d p) := by
  rw [← (qmaForkAllPortEquiv d).sum_comp f,Fintype.sum_sum_type]
  congr 1
  rw [← (Equiv.sigmaProdDistrib (fun i => Fin (d i / 2)) (Fin 2)).sum_comp]
  change (∑ p : QMAForkPair d × Fin 2, f (qmaForkPairedPort d p)) = _
  rw [Fintype.sum_prod_type,← P.pairEquiv.symm.sum_comp]

theorem next_port_sum (f : (Σ i, Fin (d i / 2 + d i % 2)) → M) :
    (∑ p, f p) =
      (∑ e : Fin P.pairCount, f (P.nextPortEquiv.symm (.inl (P.pairEquiv.symm e)))) +
      ∑ p : QMAForkRemainder d, f (P.nextPortEquiv.symm (.inr p)) := by
  rw [← P.nextPortEquiv.symm.sum_comp f,Fintype.sum_sum_type]
  congr 1
  exact (P.pairEquiv.symm.sum_comp _).symm

end QMAForkPorts
end ContinuumCoulomb

end

end OAI
