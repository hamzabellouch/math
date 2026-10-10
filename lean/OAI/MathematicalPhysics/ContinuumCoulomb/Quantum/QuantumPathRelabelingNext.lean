import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabelingProperties

namespace OAI

/-! Relabeling commutes with a scheduled subdivision. This identifies the
literal list order with the physical port graph through every round. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathRelabeling
open MediatorGraph
open scoped Classical
variable {S T : QMAPathSchedule} (E : QMAPathRelabeling S T)

def activeEquiv : {e // e ∈ S.active} ≃ {e // e ∈ T.active} :=
  Equiv.subtypeEquiv E.edge (by intro e; simp only [QMAPathSchedule.mem_active,E.work])
def retainedEquiv : {e // e ∉ S.active} ≃ {e // e ∉ T.active} :=
  Equiv.subtypeEquiv E.edge (by intro e; simp only [QMAPathSchedule.mem_active,E.work])
def activeIndex : Fin S.active.card ≃ Fin T.active.card :=
  (S.active.equivFin.symm.trans E.activeEquiv).trans T.active.equivFin

theorem selected_index (i : Fin S.active.card) :
    E.edge (qmaSelectedIndex S.active i)=qmaSelectedIndex T.active (E.activeIndex i) := by
  simp only [activeIndex,qmaSelectedIndex,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

def nextVertex : Fin (S.graph.n+S.active.card*2) ≃ Fin (T.graph.n+T.active.card*2) :=
  ((vertexEquiv _ _).symm.trans (Equiv.sumCongr E.vertex
    (Equiv.prodCongr E.activeIndex (Equiv.refl (Fin 2))))).trans (vertexEquiv _ _)
def nextEdge : QMAPartialPathsEdge S.active ≃ QMAPartialPathsEdge T.active :=
  Equiv.sumCongr E.retainedEquiv
    (Equiv.sumCongr E.activeIndex (Equiv.prodCongr E.activeIndex (Equiv.refl (Fin 2))))

theorem nextVertex_old (v : Fin S.graph.n) :
    E.nextVertex (old _ _ v)=old _ _ (E.vertex v) := by simp [nextVertex,old]
theorem nextVertex_fresh (i : Fin S.active.card) (a : Fin 2) :
    E.nextVertex (fresh _ _ i a)=fresh _ _ (E.activeIndex i) a := by
  simp [nextVertex,fresh]

theorem next_left (N : ℚ) (e : (S.next N).graph.Edge) :
    E.nextVertex ((S.next N).graph.left e)=(T.next N).graph.left (E.nextEdge e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · change E.nextVertex (old _ _ (S.graph.left e.val))=old _ _ (T.graph.left (E.edge e.val))
    rw [E.nextVertex_old,E.left]
  · exact E.nextVertex_fresh i 0
  · fin_cases a
    · change E.nextVertex (old _ _ (S.graph.left (qmaSelectedIndex S.active i)))=
        old _ _ (T.graph.left (qmaSelectedIndex T.active (E.activeIndex i)))
      rw [E.nextVertex_old,E.left,E.selected_index]
    · change E.nextVertex (old _ _ (S.graph.right (qmaSelectedIndex S.active i)))=
        old _ _ (T.graph.right (qmaSelectedIndex T.active (E.activeIndex i)))
      rw [E.nextVertex_old,E.right,E.selected_index]

theorem next_right (N : ℚ) (e : (S.next N).graph.Edge) :
    E.nextVertex ((S.next N).graph.right e)=(T.next N).graph.right (E.nextEdge e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · change E.nextVertex (old _ _ (S.graph.right e.val))=old _ _ (T.graph.right (E.edge e.val))
    rw [E.nextVertex_old,E.right]
  · exact E.nextVertex_fresh i 1
  · fin_cases a
    · exact E.nextVertex_fresh i 0
    · exact E.nextVertex_fresh i 1

theorem next_work (N : ℚ) (e : (S.next N).graph.Edge) :
    (S.next N).work e=(T.next N).work (E.nextEdge e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · rfl
  · rfl
  · change (if a=1 then S.work (qmaSelectedIndex S.active i)-1 else 0)=
      (if a=1 then T.work (qmaSelectedIndex T.active (E.activeIndex i))-1 else 0)
    rw [E.work,E.selected_index]

def next (N : ℚ) : QMAPathRelabeling (S.next N) (T.next N) where
  vertex := E.nextVertex
  edge := E.nextEdge
  left := E.next_left N
  right := E.next_right N
  work := E.next_work N

end ContinuumCoulomb.QMAPathRelabeling

end

end OAI
