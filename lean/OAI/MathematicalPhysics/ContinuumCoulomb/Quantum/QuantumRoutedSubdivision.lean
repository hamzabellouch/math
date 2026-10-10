import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathPlacement
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathScheduleSize

namespace OAI

/-! Complete odd-route realization with the actual rational Hamiltonian,
finite rectangle, degree bound and accumulated full-space spectral error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

def Bounded (X Y : ℕ) : Prop :=
  (∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y) ∧
    ∀ e k, k ≤ 2*W.work e+1 → (P.point e k).1 < X ∧ (P.point e k).2 < Y

theorem next_bounded (N : ℚ) {X Y : ℕ} (h : P.Bounded X Y) : (P.next N).Bounded X Y := by
  constructor
  · change ∀ v : Fin (W.graph.n+W.active.card*2),
      (P.nextPosition v).1 < X ∧ (P.nextPosition v).2 < Y
    intro v
    obtain ⟨v,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective v
    rcases v with v | ⟨i,b⟩
    · change (P.nextPosition (old _ _ v)).1 < X ∧ (P.nextPosition (old _ _ v)).2 < Y
      simpa only [nextPosition_old] using h.1 v
    · have hw := W.selected_work_pos i
      have hb := b.isLt
      change (P.nextPosition (fresh _ _ i b)).1 < X ∧ (P.nextPosition (fresh _ _ i b)).2 < Y
      simpa only [nextPosition_fresh,freshPosition] using
        h.2 (qmaSelectedIndex W.active i) (b.val+1) (by omega)
  · intro e k hk
    exact h.2 (W.nextParent e) (W.nextIndex e k) (W.nextIndex_bounds e hk)

def iterate (P : QMAPathEmbedding W Γ) (N : ℚ) : (k : ℕ) → QMAPathEmbedding (W.iterate N k) Γ
  | 0 => P
  | k+1 => (iterate P N k).next N

theorem iterate_bounded (N : ℚ) {X Y : ℕ} (h : P.Bounded X Y) (k : ℕ) :
    (P.iterate N k).Bounded X Y := by
  induction k with
  | zero => exact h
  | succ k ih =>
    change ((P.iterate N k).next N).Bounded X Y
    exact (P.iterate N k).next_bounded N ih

theorem realize {N : ℚ} (hN : 0 < N) {D X Y d : ℕ} (h3 : 3 ≤ d)
    (hD : ∀ e, W.work e ≤ D) (hbox : P.Bounded X Y)
    (hd : ∀ v, qmaGraphDegree W.graph.left W.graph.right v ≤ d) :
    ∃ (H : QMARationalExchangeGraph) (position : Fin H.n → ℕ × ℕ),
      Function.Injective position ∧
      (∀ v, (position v).1 < X ∧ (position v).2 < Y) ∧
      (∀ e, Γ.Adj (position (H.left e)) (position (H.right e))) ∧
      (∀ v, qmaGraphDegree H.left H.right v ≤ d) ∧
      H.n+Fintype.card H.Edge ≤ 5^D*(W.graph.n+Fintype.card W.graph.Edge) ∧
      |H.energy-W.graph.energy| ≤ (D:ℝ)/(N:ℝ) := by
  let Q := P.iterate N D
  refine ⟨(W.iterate N D).graph,Q.position,Q.position_injective,?_,?_,?_,?_,?_⟩
  · exact (P.iterate_bounded N hbox D).1
  · exact Q.adjacent_of_complete (W.iterate_complete N hD)
  · exact W.iterate_degree N h3 hd D
  · exact W.iterate_size N D
  · exact W.iterate_energy_error hN D

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
