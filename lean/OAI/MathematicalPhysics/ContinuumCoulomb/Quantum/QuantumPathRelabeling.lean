import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutedSubdivision

namespace OAI

/-! Transport of the route invariant between different finite edge orders.
This is used when the emitted list order differs from a set's chosen order. -/

noncomputable section
namespace ContinuumCoulomb

structure QMAPathRelabeling (S T : QMAPathSchedule) where
  vertex : Fin S.graph.n ≃ Fin T.graph.n
  edge : S.graph.Edge ≃ T.graph.Edge
  left : ∀ e, vertex (S.graph.left e)=T.graph.left (edge e)
  right : ∀ e, vertex (S.graph.right e)=T.graph.right (edge e)
  work : ∀ e, S.work e=T.work (edge e)

namespace QMAPathRelabeling
variable {S T : QMAPathSchedule} (E : QMAPathRelabeling S T)

theorem inverse_left (f : T.graph.Edge) :
    E.vertex.symm (T.graph.left f)=S.graph.left (E.edge.symm f) := by
  have h := congrArg E.vertex.symm (E.left (E.edge.symm f))
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using h.symm

theorem inverse_right (f : T.graph.Edge) :
    E.vertex.symm (T.graph.right f)=S.graph.right (E.edge.symm f) := by
  have h := congrArg E.vertex.symm (E.right (E.edge.symm f))
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using h.symm

theorem inverse_work (f : T.graph.Edge) : S.work (E.edge.symm f)=T.work f := by
  simpa only [Equiv.apply_symm_apply] using E.work (E.edge.symm f)

def transport {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding S Γ) : QMAPathEmbedding T Γ where
  position v := P.position (E.vertex.symm v)
  position_injective := P.position_injective.comp E.vertex.symm.injective
  point e k := P.point (E.edge.symm e) k
  first e := by rw [E.inverse_left]; exact P.first _
  last e := by rw [← E.inverse_work,E.inverse_right]; exact P.last _
  simple e i j hi hj h := by
    rw [← E.inverse_work] at hi hj
    exact P.simple _ i j hi hj h
  step e i hi := by
    rw [← E.inverse_work] at hi
    exact P.step _ i hi
  avoids e i v hi0 hi := by
    rw [← E.inverse_work] at hi
    exact P.avoids _ i _ hi0 hi
  disjoint e f i j hef hi0 hi hj := by
    rw [← E.inverse_work] at hi hj
    exact P.disjoint _ _ i j (fun h => hef (E.edge.symm.injective h)) hi0 hi hj

theorem transport_bounded {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding S Γ)
    {X Y : ℕ} (h : P.Bounded X Y) : (E.transport P).Bounded X Y := by
  constructor
  · intro v
    exact h.1 (E.vertex.symm v)
  · intro e k hk
    rw [← E.inverse_work] at hk
    exact h.2 (E.edge.symm e) k hk

end QMAPathRelabeling
end ContinuumCoulomb

end

end OAI
