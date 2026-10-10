import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathEmbedding
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathPieces

namespace OAI

/-! Physical placements are preserved by every scheduled odd subdivision. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

def nextPoint (e : QMAPartialPathsEdge W.active) (k : ℕ) : ℕ × ℕ :=
  P.point (W.nextParent e) (W.nextIndex e k)

theorem nextPoint_first (e : QMAPartialPathsEdge W.active) :
    P.nextPoint e 0 = P.nextPosition (qmaPartialPathsLeft W.graph.left W.graph.right W.active e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
      qmaParallelGraphLeft] using P.first e.val
  · simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
      qmaParallelGraphLeft,freshPosition]
  · fin_cases a
    · simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
        qmaParallelGraphLeft,qmaSelectedSite] using P.first (qmaSelectedIndex W.active i)
    · simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
        qmaParallelGraphLeft,qmaSelectedSite] using P.last (qmaSelectedIndex W.active i)

theorem nextPoint_last (e : QMAPartialPathsEdge W.active) :
    P.nextPoint e (2*W.nextWork e+1) =
      P.nextPosition (qmaPartialPathsRight W.graph.right W.active (fun _ => false) e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · have hz := W.retained_work_zero e
    simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
      qmaPartialPathsRight,qmaParallelGraphRight,hz] using P.last e.val
  · simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
      qmaPartialPathsRight,qmaParallelGraphRight,freshPosition]
  · have hw := W.selected_work_pos i
    fin_cases a
    · simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
        qmaPartialPathsRight,qmaParallelGraphRight,qmaPathMember,freshPosition]
    · have hi : 2*W.work (qmaSelectedIndex W.active i)+1 -
          (2*(W.work (qmaSelectedIndex W.active i)-1)+1) = 2 := by omega
      simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
        qmaPartialPathsRight,qmaParallelGraphRight,qmaPathMember,freshPosition,hi]

theorem nextPoint_simple (e : QMAPartialPathsEdge W.active) (i j : ℕ)
    (hi : i ≤ 2*W.nextWork e+1) (hj : j ≤ 2*W.nextWork e+1)
    (h : P.nextPoint e i = P.nextPoint e j) : i = j := by
  have he := P.simple _ _ _ (W.nextIndex_bounds e hi) (W.nextIndex_bounds e hj) h
  exact W.nextIndex_injective e hi hj he

theorem nextPoint_step (e : QMAPartialPathsEdge W.active) (i : ℕ)
    (hi : i < 2*W.nextWork e+1) : Γ.Adj (P.nextPoint e i) (P.nextPoint e (i+1)) := by
  have hb := W.nextIndex_bounds e (Nat.le_of_lt hi)
  have hn := W.nextIndex_bounds e (k := i+1) (Nat.succ_le_iff.mpr hi)
  rcases W.nextIndex_step e hi with h | h
  · have hk : W.nextIndex e i < 2*W.work (W.nextParent e)+1 := by omega
    simpa only [nextPoint,h] using P.step (W.nextParent e) (W.nextIndex e i) hk
  · have hk : W.nextIndex e (i+1) < 2*W.work (W.nextParent e)+1 := by omega
    simpa only [nextPoint,h] using (P.step (W.nextParent e) (W.nextIndex e (i+1)) hk).symm

theorem nextPoint_avoids (e : QMAPartialPathsEdge W.active) (i : ℕ)
    (v : Fin (W.graph.n+W.active.card*2)) (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1) :
    P.nextPoint e i ≠ P.nextPosition v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective v
  obtain ⟨hlo,hhi⟩ := W.nextIndex_interior e hi0 hi
  rcases v with v | ⟨a,b⟩
  · change P.point (W.nextParent e) (W.nextIndex e i) ≠ P.nextPosition (old _ _ v)
    rw [nextPosition_old]
    exact P.avoids _ _ v (by omega) hhi
  · simp only [show vertexEquiv W.graph.n W.active.card (Sum.inr (a,b)) = fresh _ _ a b from rfl,
      nextPosition_fresh,freshPosition,nextPoint]
    intro h
    have hp := W.selected_work_pos a
    have hb := b.isLt
    by_cases he : W.nextParent e = qmaSelectedIndex W.active a
    · have hi' : W.nextIndex e i ≤ 2*W.work (qmaSelectedIndex W.active a)+1 := by
        rw [← he]
        omega
      have hj' : b.val+1 ≤ 2*W.work (qmaSelectedIndex W.active a)+1 := by omega
      rw [he] at h
      have hx := P.simple _ _ _ hi' hj' h
      omega
    · exact P.disjoint _ _ _ _ he (by omega) hhi (by omega) h

theorem nextPoint_disjoint (e f : QMAPartialPathsEdge W.active) (i j : ℕ)
    (hef : e ≠ f) (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1) (hj : j ≤ 2*W.nextWork f+1) :
    P.nextPoint e i ≠ P.nextPoint f j := by
  intro h
  obtain ⟨hlo,hhi⟩ := W.nextIndex_interior e hi0 hi
  have hbj := W.nextIndex_bounds f hj
  have he : W.nextParent e = W.nextParent f := by
    by_contra hn
    exact P.disjoint _ _ _ _ hn (by omega) hhi hbj h
  have hbi := W.nextIndex_bounds e (Nat.le_of_lt hi)
  change P.point (W.nextParent e) (W.nextIndex e i) =
    P.point (W.nextParent f) (W.nextIndex f j) at h
  rw [← he] at h hbj
  have hx := P.simple _ _ _ hbi hbj h
  exact hef (W.nextIndex_separated e f hi0 hi hj he hx)

def next (N : ℚ) : QMAPathEmbedding (W.next N) Γ where
  position := P.nextPosition
  position_injective := P.nextPosition_injective
  point := P.nextPoint
  first := P.nextPoint_first
  last := P.nextPoint_last
  simple := P.nextPoint_simple
  step := P.nextPoint_step
  avoids := P.nextPoint_avoids
  disjoint := P.nextPoint_disjoint

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
