import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedCounts
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedBounds

namespace OAI

/-! Explicit rectangular bounds for every vertex and every buffered route. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCellCoordinate_lt {W x X z : ℕ} (hx : x < X) (hz : z < W) :
    W*x+z < W*X := by
  calc
    W*x+z < W*x+W := Nat.add_lt_add_left hz _
    _ = W*(x+1) := by ring
    _ ≤ W*X := Nat.mul_le_mul_left W (by omega)

theorem qmaManhattanSupport_rectangle {p q z : ℕ × ℕ} {X Y : ℕ}
    (hp : p.1 < X ∧ p.2 < Y) (hq : q.1 < X ∧ q.2 < Y)
    (hz : qmaManhattanSupport p q z) : z.1 < X ∧ z.2 < Y := by
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩ <;> unfold qmaBetween at * <;> omega

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def bufferedWidth : ℕ := 8*(9*B+9)*((M.rows+1)*A)
def bufferedHeight : ℕ := 8*(9*B+9)*(M.width+1)

theorem routeVertex_bounds (v : Fin M.n) :
    (M.routeVertex v).1 < (M.rows+1)*A ∧ (M.routeVertex v).2 < M.width+1 :=
  ⟨(M.qubitSlots.site v).1.isLt,(M.qubitSlots.site v).2.isLt⟩

theorem placedVertex_bounds (v : Fin M.n) :
    (M.placedVertex v).1 < M.bufferedWidth ∧ (M.placedVertex v).2 < M.bufferedHeight := by
  have hb := M.routeVertex_bounds v
  exact ⟨qmaCellCoordinate_lt hb.1 (by omega),qmaCellCoordinate_lt hb.2 (by omega)⟩

theorem endpointArmSupport_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ} (hz : M.endpointArmSupport hd v e z) :
    z.1 < M.bufferedWidth ∧ z.2 < M.bufferedHeight := by
  obtain ⟨p,hp,hs⟩ := hz
  have hb := M.routeVertex_bounds v
  have hs' := qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) _ hs
  rw [← hp]
  exact ⟨qmaCellCoordinate_lt hb.1 hs'.2.1,qmaCellCoordinate_lt hb.2 hs'.2.2.2⟩

theorem spacedSupport_bounds (e : M.Term) {z : ℕ × ℕ} (hz : M.spacedSupport e z) :
    z.1 < M.bufferedWidth ∧ z.2 < M.bufferedHeight := by
  have bound (v : Fin M.n) :
      (qmaLanePoint (M.spacedColor e) (M.routeVertex v)).1 < M.bufferedWidth ∧
        (qmaLanePoint (M.spacedColor e) (M.routeVertex v)).2 < M.bufferedHeight := by
    have hb := M.routeVertex_bounds v
    exact ⟨qmaCellCoordinate_lt hb.1 (M.spacedColor e).isLt,
      qmaCellCoordinate_lt hb.2 (M.spacedColor e).isLt⟩
  exact qmaManhattanSupport_rectangle (bound (M.left e)) (bound (M.right e)) hz

theorem bufferedPath_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {z : ℕ × ℕ} (hz : z ∈ (M.bufferedPath hd e).val.support) :
    z.1 < M.bufferedWidth ∧ z.2 < M.bufferedHeight := by
  rcases M.bufferedPath_support hd e hz with h | h | h
  · exact M.endpointArmSupport_bounds hd _ _ h
  · exact M.spacedSupport_bounds e h
  · exact M.endpointArmSupport_bounds hd _ _ h

def routedVertices (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) : Finset (ℕ × ℕ) :=
  (Finset.univ.image M.placedVertex) ∪ M.bufferedAllSites hd

theorem routedVertices_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    {z : ℕ × ℕ} (hz : z ∈ M.routedVertices hd) :
    z.1 < M.bufferedWidth ∧ z.2 < M.bufferedHeight := by
  rcases Finset.mem_union.mp hz with h | h
  · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp h
    exact M.placedVertex_bounds v
  · obtain ⟨e,_,he⟩ := Finset.mem_biUnion.mp h
    exact M.bufferedPath_bounds hd e (List.mem_toFinset.mp he)

theorem routedVertices_card (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    (M.routedVertices hd).card ≤ M.n+
      Fintype.card M.Term*(2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2)+1) := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    ((Finset.card_image_le).trans_eq (by simp)) (M.bufferedAllSites_card hd))

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
