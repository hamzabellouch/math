import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathCoverage

namespace OAI

/-! Subdivision only introduces spins at prescribed route points. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

theorem next_occupied_source (N : ℚ) {z : ℕ × ℕ} (hz : (P.next N).Occupied z) : P.Occupied z := by
  rcases hz with ⟨v,hv⟩ | ⟨e,k,hk,hz⟩
  · obtain ⟨v,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective v
    rcases v with v | ⟨i,b⟩
    · change P.nextPosition (old _ _ v) = z at hv
      rw [P.nextPosition_old] at hv
      exact Or.inl ⟨v,hv⟩
    · change P.nextPosition (fresh _ _ i b) = z at hv
      rw [P.nextPosition_fresh] at hv
      have hw := W.selected_work_pos i
      have hb := b.isLt
      exact Or.inr ⟨qmaSelectedIndex W.active i,b.val+1,by omega,hv⟩
  · change P.point (W.nextParent e) (W.nextIndex e k) = z at hz
    exact Or.inr ⟨W.nextParent e,W.nextIndex e k,W.nextIndex_bounds e hk,hz⟩

theorem iterate_occupied_source (N : ℚ) (k : ℕ) {z : ℕ × ℕ}
    (hz : (P.iterate N k).Occupied z) : P.Occupied z := by
  induction k with
  | zero => exact hz
  | succ k ih => exact ih ((P.iterate N k).next_occupied_source N hz)

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
