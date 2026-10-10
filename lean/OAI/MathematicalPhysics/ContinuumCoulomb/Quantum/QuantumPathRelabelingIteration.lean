import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabelingNext

namespace OAI

/-! Finite route relabeling preserves the actual coordinates at every
scheduled subdivision round. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathRelabeling
open MediatorGraph
open scoped Classical
variable {S T U : QMAPathSchedule}

def refl (S : QMAPathSchedule) : QMAPathRelabeling S S where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  left _ := rfl
  right _ := rfl
  work _ := rfl

def trans (E : QMAPathRelabeling S T) (F : QMAPathRelabeling T U) :
    QMAPathRelabeling S U where
  vertex := E.vertex.trans F.vertex
  edge := E.edge.trans F.edge
  left e := by simp only [Equiv.trans_apply,E.left,F.left]
  right e := by simp only [Equiv.trans_apply,E.right,F.right]
  work e := (E.work e).trans (F.work _)

variable (E : QMAPathRelabeling S T)
variable {Γ : SimpleGraph (ℕ × ℕ)}
    (P : QMAPathEmbedding S Γ) (Q : QMAPathEmbedding T Γ)
    (hpos : ∀ v, Q.position (E.vertex v)=P.position v)
    (hpoint : ∀ e k, Q.point (E.edge e) k=P.point e k)

include hpos hpoint in
theorem next_position (N : ℚ) (v : Fin (S.next N).graph.n) :
    (Q.next N).position ((E.next N).vertex v)=(P.next N).position v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv S.graph.n S.active.card).surjective v
  rcases v with v | ⟨i,a⟩
  · change Q.nextPosition (E.nextVertex (old _ _ v))=P.nextPosition (old _ _ v)
    rw [E.nextVertex_old,QMAPathEmbedding.nextPosition_old,
      QMAPathEmbedding.nextPosition_old]
    exact hpos v
  · change Q.nextPosition (E.nextVertex (fresh _ _ i a))=P.nextPosition (fresh _ _ i a)
    rw [E.nextVertex_fresh,QMAPathEmbedding.nextPosition_fresh,
      QMAPathEmbedding.nextPosition_fresh]
    change Q.point (qmaSelectedIndex T.active (E.activeIndex i)) (a.val+1)=
      P.point (qmaSelectedIndex S.active i) (a.val+1)
    rw [← E.selected_index]
    exact hpoint _ _

include hpoint in
theorem next_point (N : ℚ) (e : (S.next N).graph.Edge) (k : ℕ) :
    (Q.next N).point ((E.next N).edge e) k=(P.next N).point e k := by
  rcases e with e | (i | ⟨i,a⟩)
  · exact hpoint e.val k
  · change Q.point (qmaSelectedIndex T.active (E.activeIndex i)) (k+1)=
      P.point (qmaSelectedIndex S.active i) (k+1)
    rw [← E.selected_index]
    exact hpoint _ _
  · change Q.point (qmaSelectedIndex T.active (E.activeIndex i))
        (if a=0 then k else 2*T.work (qmaSelectedIndex T.active (E.activeIndex i))+1-k)=
      P.point (qmaSelectedIndex S.active i)
        (if a=0 then k else 2*S.work (qmaSelectedIndex S.active i)+1-k)
    rw [← E.selected_index,← E.work]
    exact hpoint _ _

def iterate (N : ℚ) : (k : ℕ) → QMAPathRelabeling (S.iterate N k) (T.iterate N k)
  | 0 => E
  | k+1 => (iterate N k).next N

include hpoint in
theorem iterate_point (N : ℚ) (k : ℕ) :
    ∀ e j, (Q.iterate N k).point ((E.iterate N k).edge e) j=(P.iterate N k).point e j := by
  induction k with
  | zero => exact hpoint
  | succ k ih => exact (E.iterate N k).next_point (P.iterate N k) (Q.iterate N k) ih N

include hpos hpoint in
theorem iterate_position (N : ℚ) (k : ℕ) :
    ∀ v, (Q.iterate N k).position ((E.iterate N k).vertex v)=(P.iterate N k).position v := by
  induction k with
  | zero => exact hpos
  | succ k ih =>
    exact (E.iterate N k).next_position (P.iterate N k) (Q.iterate N k) ih
      (E.iterate_point P Q hpoint N k) N


end ContinuumCoulomb.QMAPathRelabeling

end

end OAI
